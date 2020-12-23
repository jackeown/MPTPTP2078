%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:56 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 (1150 expanded)
%              Number of clauses        :   69 ( 523 expanded)
%              Number of leaves         :   14 ( 284 expanded)
%              Depth                    :   29
%              Number of atoms          :  383 (4977 expanded)
%              Number of equality atoms :   50 ( 689 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t56_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k3_tarski(X1),X2)
        & r2_hidden(X3,X1) )
     => r1_tarski(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

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

fof(c_0_14,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X22,X21)
        | r2_hidden(X22,X21)
        | v1_xboole_0(X21) )
      & ( ~ r2_hidden(X22,X21)
        | m1_subset_1(X22,X21)
        | v1_xboole_0(X21) )
      & ( ~ m1_subset_1(X22,X21)
        | v1_xboole_0(X22)
        | ~ v1_xboole_0(X21) )
      & ( ~ v1_xboole_0(X22)
        | m1_subset_1(X22,X21)
        | ~ v1_xboole_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_15,plain,(
    ! [X42] :
      ( ~ l1_pre_topc(X42)
      | m1_subset_1(u1_pre_topc(X42),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X42)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk7_0))) != u1_struct_0(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_21,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(k3_tarski(X27),X28)
      | ~ r2_hidden(X29,X27)
      | r1_tarski(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X23,X24] :
      ( ( ~ m1_setfam_1(X24,X23)
        | r1_tarski(X23,k3_tarski(X24)) )
      & ( ~ r1_tarski(X23,k3_tarski(X24))
        | m1_setfam_1(X24,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(k3_tarski(X18),k3_tarski(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_25,plain,(
    ! [X20] : k3_tarski(k1_zfmisc_1(X20)) = X20 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_26,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))
    | r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( v1_xboole_0(u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

fof(c_0_38,plain,(
    ! [X33,X34] :
      ( ( ~ m1_setfam_1(X34,X33)
        | k5_setfam_1(X33,X34) = X33
        | ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(X33))) )
      & ( k5_setfam_1(X33,X34) != X33
        | m1_setfam_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_39,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( k3_tarski(X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_43,plain,(
    ! [X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(X9,esk1_3(X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k3_tarski(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_tarski(X7) )
      & ( ~ r2_hidden(X11,X12)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k3_tarski(X7) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_hidden(esk2_2(X13,X14),X16)
        | ~ r2_hidden(X16,X13)
        | X14 = k3_tarski(X13) )
      & ( r2_hidden(esk2_2(X13,X14),esk3_2(X13,X14))
        | r2_hidden(esk2_2(X13,X14),X14)
        | X14 = k3_tarski(X13) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | r2_hidden(esk2_2(X13,X14),X14)
        | X14 = k3_tarski(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_44,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))
      | k5_setfam_1(X25,X26) = k3_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))
    | r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk7_0))
    | r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_27])])).

cnf(c_0_47,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( m1_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( k3_tarski(X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_50,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | ~ v1_xboole_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))
    | r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,plain,
    ( k5_setfam_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( k3_tarski(X1) = X2
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( X1 = k3_tarski(X2)
    | m1_subset_1(esk3_2(X2,X1),X2)
    | v1_xboole_0(X2)
    | r2_hidden(esk2_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_60,plain,(
    ! [X43] :
      ( v1_xboole_0(X43)
      | ~ r2_hidden(k3_tarski(X43),X43)
      | k4_yellow_0(k2_yellow_1(X43)) = k3_tarski(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_61,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) = k3_tarski(u1_pre_topc(esk7_0))
    | r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_19])).

cnf(c_0_63,plain,
    ( k3_tarski(X1) = X2
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( X1 = X2
    | v1_xboole_0(k1_zfmisc_1(X2))
    | r2_hidden(esk2_2(k1_zfmisc_1(X2),X1),X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,esk3_2(k1_zfmisc_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_34])).

cnf(c_0_65,plain,
    ( r2_hidden(esk2_2(X1,X2),esk3_2(X1,X2))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk7_0)) = u1_struct_0(esk7_0)
    | ~ r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_27])]),c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk7_0))) != u1_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_69,plain,
    ( X1 = X2
    | v1_xboole_0(k1_zfmisc_1(X2))
    | r2_hidden(esk2_2(k1_zfmisc_1(X2),X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_34])])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk7_0))
    | ~ r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

fof(c_0_71,plain,(
    ! [X35,X36,X37,X38] :
      ( ( r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ m1_subset_1(X36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r1_tarski(X36,u1_pre_topc(X35))
        | r2_hidden(k5_setfam_1(u1_struct_0(X35),X36),u1_pre_topc(X35))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ r2_hidden(X37,u1_pre_topc(X35))
        | ~ r2_hidden(X38,u1_pre_topc(X35))
        | r2_hidden(k9_subset_1(u1_struct_0(X35),X37,X38),u1_pre_topc(X35))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk5_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk6_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk5_1(X35),u1_pre_topc(X35))
        | m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk6_1(X35),u1_pre_topc(X35))
        | m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X35),esk5_1(X35),esk6_1(X35)),u1_pre_topc(X35))
        | m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk5_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | r1_tarski(esk4_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk6_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | r1_tarski(esk4_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk5_1(X35),u1_pre_topc(X35))
        | r1_tarski(esk4_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk6_1(X35),u1_pre_topc(X35))
        | r1_tarski(esk4_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X35),esk5_1(X35),esk6_1(X35)),u1_pre_topc(X35))
        | r1_tarski(esk4_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk5_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk6_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk5_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk6_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X35),esk5_1(X35),esk6_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_72,negated_conjecture,
    ( X1 = u1_pre_topc(esk7_0)
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | r2_hidden(esk2_2(k1_zfmisc_1(u1_pre_topc(esk7_0)),X1),X1)
    | ~ r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_75,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(esk2_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_76,negated_conjecture,
    ( X1 = u1_pre_topc(esk7_0)
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | r2_hidden(esk2_2(k1_zfmisc_1(u1_pre_topc(esk7_0)),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_27])])).

cnf(c_0_77,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_78,negated_conjecture,
    ( X1 = u1_pre_topc(esk7_0)
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk7_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_34])]),c_0_76])).

cnf(c_0_79,plain,
    ( r2_hidden(esk1_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( esk1_3(k1_zfmisc_1(u1_pre_topc(esk7_0)),u1_pre_topc(esk7_0),X1) = u1_pre_topc(esk7_0)
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_34]),c_0_34])).

cnf(c_0_81,plain,
    ( r2_hidden(esk1_3(k1_zfmisc_1(X1),X1,X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_34])).

cnf(c_0_82,negated_conjecture,
    ( esk1_3(k1_zfmisc_1(u1_pre_topc(esk7_0)),u1_pre_topc(esk7_0),u1_struct_0(esk7_0)) = u1_pre_topc(esk7_0)
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_73]),c_0_74]),c_0_27])])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_73]),c_0_74]),c_0_27])])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k1_zfmisc_1(u1_pre_topc(esk7_0)),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ v1_xboole_0(u1_pre_topc(esk7_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_73]),c_0_74]),c_0_27])])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_79]),c_0_34])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_73]),c_0_74]),c_0_27])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))
    | ~ r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_70])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_94]),c_0_70])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(X1,u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_73]),c_0_74]),c_0_27])])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_73]),c_0_74]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:09:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.053 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.21/0.45  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.21/0.45  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.21/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.45  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.21/0.45  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.21/0.45  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.21/0.45  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.21/0.45  fof(t60_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.21/0.45  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.21/0.45  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.21/0.45  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.21/0.45  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.21/0.45  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.21/0.45  fof(c_0_14, plain, ![X21, X22]:(((~m1_subset_1(X22,X21)|r2_hidden(X22,X21)|v1_xboole_0(X21))&(~r2_hidden(X22,X21)|m1_subset_1(X22,X21)|v1_xboole_0(X21)))&((~m1_subset_1(X22,X21)|v1_xboole_0(X22)|~v1_xboole_0(X21))&(~v1_xboole_0(X22)|m1_subset_1(X22,X21)|~v1_xboole_0(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.21/0.45  fof(c_0_15, plain, ![X42]:(~l1_pre_topc(X42)|m1_subset_1(u1_pre_topc(X42),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X42))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.21/0.45  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.21/0.45  fof(c_0_17, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.45  cnf(c_0_18, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.45  cnf(c_0_19, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.45  fof(c_0_20, negated_conjecture, (((~v2_struct_0(esk7_0)&v2_pre_topc(esk7_0))&l1_pre_topc(esk7_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk7_0)))!=u1_struct_0(esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.21/0.45  fof(c_0_21, plain, ![X27, X28, X29]:(~r1_tarski(k3_tarski(X27),X28)|~r2_hidden(X29,X27)|r1_tarski(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.21/0.45  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.45  fof(c_0_23, plain, ![X23, X24]:((~m1_setfam_1(X24,X23)|r1_tarski(X23,k3_tarski(X24)))&(~r1_tarski(X23,k3_tarski(X24))|m1_setfam_1(X24,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.21/0.45  fof(c_0_24, plain, ![X18, X19]:(~r1_tarski(X18,X19)|r1_tarski(k3_tarski(X18),k3_tarski(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.21/0.45  fof(c_0_25, plain, ![X20]:k3_tarski(k1_zfmisc_1(X20))=X20, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.21/0.45  cnf(c_0_26, plain, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.45  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_28, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.45  cnf(c_0_29, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.45  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.21/0.45  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.45  cnf(c_0_32, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.45  cnf(c_0_33, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.45  cnf(c_0_34, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.45  cnf(c_0_35, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.45  cnf(c_0_36, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))|r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.45  cnf(c_0_37, plain, (v1_xboole_0(u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_28, c_0_19])).
% 0.21/0.45  fof(c_0_38, plain, ![X33, X34]:((~m1_setfam_1(X34,X33)|k5_setfam_1(X33,X34)=X33|~m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(X33))))&(k5_setfam_1(X33,X34)!=X33|m1_setfam_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).
% 0.21/0.45  cnf(c_0_39, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.45  cnf(c_0_40, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.45  cnf(c_0_41, plain, (k3_tarski(X1)=X2|~m1_setfam_1(X1,X2)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.45  cnf(c_0_42, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.45  fof(c_0_43, plain, ![X7, X8, X9, X11, X12, X13, X14, X16]:((((r2_hidden(X9,esk1_3(X7,X8,X9))|~r2_hidden(X9,X8)|X8!=k3_tarski(X7))&(r2_hidden(esk1_3(X7,X8,X9),X7)|~r2_hidden(X9,X8)|X8!=k3_tarski(X7)))&(~r2_hidden(X11,X12)|~r2_hidden(X12,X7)|r2_hidden(X11,X8)|X8!=k3_tarski(X7)))&((~r2_hidden(esk2_2(X13,X14),X14)|(~r2_hidden(esk2_2(X13,X14),X16)|~r2_hidden(X16,X13))|X14=k3_tarski(X13))&((r2_hidden(esk2_2(X13,X14),esk3_2(X13,X14))|r2_hidden(esk2_2(X13,X14),X14)|X14=k3_tarski(X13))&(r2_hidden(esk3_2(X13,X14),X13)|r2_hidden(esk2_2(X13,X14),X14)|X14=k3_tarski(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.21/0.45  fof(c_0_44, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))|k5_setfam_1(X25,X26)=k3_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.21/0.45  cnf(c_0_45, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))|r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.45  cnf(c_0_46, negated_conjecture, (v1_xboole_0(u1_pre_topc(esk7_0))|r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_27])])).
% 0.21/0.45  cnf(c_0_47, plain, (k5_setfam_1(X2,X1)=X2|~m1_setfam_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.45  cnf(c_0_48, plain, (m1_setfam_1(X1,X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.45  cnf(c_0_49, plain, (k3_tarski(X1)=X2|~m1_setfam_1(X1,X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.45  fof(c_0_50, plain, ![X30, X31, X32]:(~r2_hidden(X30,X31)|~m1_subset_1(X31,k1_zfmisc_1(X32))|~v1_xboole_0(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.21/0.45  cnf(c_0_51, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.45  cnf(c_0_52, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.45  cnf(c_0_53, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.45  cnf(c_0_54, negated_conjecture, (m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))|r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.45  cnf(c_0_55, plain, (k5_setfam_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.45  cnf(c_0_56, plain, (k3_tarski(X1)=X2|~r2_hidden(X2,X1)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_49, c_0_48])).
% 0.21/0.45  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.21/0.45  cnf(c_0_58, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.45  cnf(c_0_59, plain, (X1=k3_tarski(X2)|m1_subset_1(esk3_2(X2,X1),X2)|v1_xboole_0(X2)|r2_hidden(esk2_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.45  fof(c_0_60, plain, ![X43]:(v1_xboole_0(X43)|(~r2_hidden(k3_tarski(X43),X43)|k4_yellow_0(k2_yellow_1(X43))=k3_tarski(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.21/0.45  cnf(c_0_61, negated_conjecture, (k5_setfam_1(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))=k3_tarski(u1_pre_topc(esk7_0))|r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.45  cnf(c_0_62, plain, (k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_55, c_0_19])).
% 0.21/0.45  cnf(c_0_63, plain, (k3_tarski(X1)=X2|~r2_hidden(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.45  cnf(c_0_64, plain, (X1=X2|v1_xboole_0(k1_zfmisc_1(X2))|r2_hidden(esk2_2(k1_zfmisc_1(X2),X1),X1)|~v1_xboole_0(X2)|~r2_hidden(X3,esk3_2(k1_zfmisc_1(X2),X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_34])).
% 0.21/0.45  cnf(c_0_65, plain, (r2_hidden(esk2_2(X1,X2),esk3_2(X1,X2))|r2_hidden(esk2_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.45  cnf(c_0_66, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.45  cnf(c_0_67, negated_conjecture, (k3_tarski(u1_pre_topc(esk7_0))=u1_struct_0(esk7_0)|~r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_27])]), c_0_63])).
% 0.21/0.45  cnf(c_0_68, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk7_0)))!=u1_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_69, plain, (X1=X2|v1_xboole_0(k1_zfmisc_1(X2))|r2_hidden(esk2_2(k1_zfmisc_1(X2),X1),X1)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_34])])).
% 0.21/0.45  cnf(c_0_70, negated_conjecture, (v1_xboole_0(u1_pre_topc(esk7_0))|~r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.21/0.45  fof(c_0_71, plain, ![X35, X36, X37, X38]:((((r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))|~v2_pre_topc(X35)|~l1_pre_topc(X35))&(~m1_subset_1(X36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|(~r1_tarski(X36,u1_pre_topc(X35))|r2_hidden(k5_setfam_1(u1_struct_0(X35),X36),u1_pre_topc(X35)))|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X35)))|(~r2_hidden(X37,u1_pre_topc(X35))|~r2_hidden(X38,u1_pre_topc(X35))|r2_hidden(k9_subset_1(u1_struct_0(X35),X37,X38),u1_pre_topc(X35))))|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(((m1_subset_1(esk5_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&((m1_subset_1(esk6_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(((r2_hidden(esk5_1(X35),u1_pre_topc(X35))|(m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(r2_hidden(esk6_1(X35),u1_pre_topc(X35))|(m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~r2_hidden(k9_subset_1(u1_struct_0(X35),esk5_1(X35),esk6_1(X35)),u1_pre_topc(X35))|(m1_subset_1(esk4_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))))&(((m1_subset_1(esk5_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(r1_tarski(esk4_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&((m1_subset_1(esk6_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(r1_tarski(esk4_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(((r2_hidden(esk5_1(X35),u1_pre_topc(X35))|(r1_tarski(esk4_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(r2_hidden(esk6_1(X35),u1_pre_topc(X35))|(r1_tarski(esk4_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~r2_hidden(k9_subset_1(u1_struct_0(X35),esk5_1(X35),esk6_1(X35)),u1_pre_topc(X35))|(r1_tarski(esk4_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))))&((m1_subset_1(esk5_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&((m1_subset_1(esk6_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(((r2_hidden(esk5_1(X35),u1_pre_topc(X35))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(r2_hidden(esk6_1(X35),u1_pre_topc(X35))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~r2_hidden(k9_subset_1(u1_struct_0(X35),esk5_1(X35),esk6_1(X35)),u1_pre_topc(X35))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk4_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.21/0.45  cnf(c_0_72, negated_conjecture, (X1=u1_pre_topc(esk7_0)|v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))|r2_hidden(esk2_2(k1_zfmisc_1(u1_pre_topc(esk7_0)),X1),X1)|~r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.21/0.45  cnf(c_0_73, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.21/0.45  cnf(c_0_74, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_75, plain, (X2=k3_tarski(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(esk2_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.45  cnf(c_0_76, negated_conjecture, (X1=u1_pre_topc(esk7_0)|v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))|r2_hidden(esk2_2(k1_zfmisc_1(u1_pre_topc(esk7_0)),X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_27])])).
% 0.21/0.45  cnf(c_0_77, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.45  cnf(c_0_78, negated_conjecture, (X1=u1_pre_topc(esk7_0)|v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))|~r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk7_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_34])]), c_0_76])).
% 0.21/0.45  cnf(c_0_79, plain, (r2_hidden(esk1_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_77])).
% 0.21/0.45  cnf(c_0_80, negated_conjecture, (esk1_3(k1_zfmisc_1(u1_pre_topc(esk7_0)),u1_pre_topc(esk7_0),X1)=u1_pre_topc(esk7_0)|v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))|~r2_hidden(X1,u1_pre_topc(esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_34]), c_0_34])).
% 0.21/0.45  cnf(c_0_81, plain, (r2_hidden(esk1_3(k1_zfmisc_1(X1),X1,X2),k1_zfmisc_1(X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_79, c_0_34])).
% 0.21/0.45  cnf(c_0_82, negated_conjecture, (esk1_3(k1_zfmisc_1(u1_pre_topc(esk7_0)),u1_pre_topc(esk7_0),u1_struct_0(esk7_0))=u1_pre_topc(esk7_0)|v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_73]), c_0_74]), c_0_27])])).
% 0.21/0.45  cnf(c_0_83, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))|r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))|~r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.21/0.45  cnf(c_0_84, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))|r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_73]), c_0_74]), c_0_27])])).
% 0.21/0.45  cnf(c_0_85, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk7_0)))|r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_84])).
% 0.21/0.45  cnf(c_0_86, negated_conjecture, (m1_subset_1(k1_zfmisc_1(u1_pre_topc(esk7_0)),k1_zfmisc_1(u1_pre_topc(esk7_0)))|r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))), inference(spm,[status(thm)],[c_0_85, c_0_84])).
% 0.21/0.45  cnf(c_0_87, negated_conjecture, (r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))|~v1_xboole_0(u1_pre_topc(esk7_0))|~r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk7_0)))), inference(spm,[status(thm)],[c_0_58, c_0_86])).
% 0.21/0.45  cnf(c_0_88, negated_conjecture, (r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))|~r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))|~r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk7_0)))), inference(spm,[status(thm)],[c_0_87, c_0_70])).
% 0.21/0.45  cnf(c_0_89, negated_conjecture, (r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))|~r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_73]), c_0_74]), c_0_27])])).
% 0.21/0.45  cnf(c_0_90, negated_conjecture, (r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))|~r2_hidden(X1,u1_pre_topc(esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_79]), c_0_34])).
% 0.21/0.45  cnf(c_0_91, negated_conjecture, (r2_hidden(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_73]), c_0_74]), c_0_27])])).
% 0.21/0.45  cnf(c_0_92, negated_conjecture, (m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))|v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk7_0)))), inference(spm,[status(thm)],[c_0_51, c_0_91])).
% 0.21/0.45  cnf(c_0_93, negated_conjecture, (m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))|m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk7_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_92])).
% 0.21/0.45  cnf(c_0_94, negated_conjecture, (m1_subset_1(u1_pre_topc(esk7_0),k1_zfmisc_1(u1_pre_topc(esk7_0)))|~r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(spm,[status(thm)],[c_0_93, c_0_70])).
% 0.21/0.45  cnf(c_0_95, negated_conjecture, (~r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))|~r2_hidden(X1,u1_pre_topc(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_94]), c_0_70])).
% 0.21/0.45  cnf(c_0_96, negated_conjecture, (~r2_hidden(X1,u1_pre_topc(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_73]), c_0_74]), c_0_27])])).
% 0.21/0.45  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_73]), c_0_74]), c_0_27])]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 98
% 0.21/0.45  # Proof object clause steps            : 69
% 0.21/0.45  # Proof object formula steps           : 29
% 0.21/0.45  # Proof object conjectures             : 33
% 0.21/0.45  # Proof object clause conjectures      : 30
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 24
% 0.21/0.45  # Proof object initial formulas used   : 14
% 0.21/0.45  # Proof object generating inferences   : 43
% 0.21/0.45  # Proof object simplifying inferences  : 39
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 14
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 46
% 0.21/0.45  # Removed in clause preprocessing      : 0
% 0.21/0.45  # Initial clauses in saturation        : 46
% 0.21/0.45  # Processed clauses                    : 377
% 0.21/0.45  # ...of these trivial                  : 2
% 0.21/0.45  # ...subsumed                          : 109
% 0.21/0.45  # ...remaining for further processing  : 266
% 0.21/0.45  # Other redundant clauses eliminated   : 5
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 17
% 0.21/0.45  # Backward-rewritten                   : 18
% 0.21/0.45  # Generated clauses                    : 983
% 0.21/0.45  # ...of the previous two non-trivial   : 902
% 0.21/0.45  # Contextual simplify-reflections      : 7
% 0.21/0.45  # Paramodulations                      : 976
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 5
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 179
% 0.21/0.45  #    Positive orientable unit clauses  : 8
% 0.21/0.45  #    Positive unorientable unit clauses: 0
% 0.21/0.45  #    Negative unit clauses             : 3
% 0.21/0.45  #    Non-unit-clauses                  : 168
% 0.21/0.45  # Current number of unprocessed clauses: 553
% 0.21/0.45  # ...number of literals in the above   : 2185
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 82
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 3719
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 2110
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 131
% 0.21/0.45  # Unit Clause-clause subsumption calls : 35
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 2
% 0.21/0.45  # BW rewrite match successes           : 2
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 19277
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.098 s
% 0.21/0.45  # System time              : 0.008 s
% 0.21/0.45  # Total time               : 0.107 s
% 0.21/0.45  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
