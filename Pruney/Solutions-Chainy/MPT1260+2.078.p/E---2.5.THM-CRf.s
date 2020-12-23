%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:26 EST 2020

% Result     : Theorem 5.28s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :   96 (1811 expanded)
%              Number of clauses        :   73 ( 907 expanded)
%              Number of leaves         :   11 ( 435 expanded)
%              Depth                    :   18
%              Number of atoms          :  283 (4801 expanded)
%              Number of equality atoms :   89 (2100 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_11,plain,(
    ! [X24,X25] : k4_xboole_0(X24,X25) = k5_xboole_0(X24,k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X29,X30] : k1_setfam_1(k2_tarski(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k4_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X23] : k3_xboole_0(X23,X23) = X23 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

fof(c_0_23,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k7_subset_1(X26,X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_32,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,X1) = X1
    | r2_hidden(esk2_3(X1,X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_35,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_36,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_30,c_0_15])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_3(X1,X1,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X35,X36,X37,X38] :
      ( ( ~ v3_pre_topc(X38,X36)
        | k1_tops_1(X36,X38) = X38
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X36)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( k1_tops_1(X35,X37) != X37
        | v3_pre_topc(X37,X35)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X36)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

fof(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_33])).

cnf(c_0_46,plain,
    ( k7_subset_1(X1,X2,X2) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_27])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk2_3(X2,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | r2_hidden(esk2_3(X1,X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_42])).

fof(c_0_49,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | k1_tops_1(X39,X40) = k7_subset_1(u1_struct_0(X39),X40,k2_tops_1(X39,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_50,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k7_subset_1(X2,X1,X4))
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_56,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | m1_subset_1(k2_pre_topc(X31,X32),k1_zfmisc_1(u1_struct_0(X31))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_57,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k7_subset_1(X2,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_58,plain,
    ( X1 = X2
    | r2_hidden(esk2_3(X1,X1,X1),X1)
    | r2_hidden(esk2_3(X2,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,k2_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( k7_subset_1(X1,X2,X2) = X3
    | r2_hidden(esk2_3(X3,X3,X3),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r2_hidden(X3,k2_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_51]),c_0_53])])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,k2_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_53]),c_0_51])])).

cnf(c_0_67,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0) = X1
    | r2_hidden(esk2_3(X1,X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(X1,k2_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_53]),c_0_51])]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k5_xboole_0(X1,X1) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( X1 = k1_setfam_1(k2_tarski(X2,k2_tops_1(esk3_0,esk4_0)))
    | r2_hidden(esk1_3(X2,k2_tops_1(esk3_0,esk4_0),X1),X1)
    | ~ r2_hidden(esk1_3(X2,k2_tops_1(esk3_0,esk4_0),X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_35])).

cnf(c_0_71,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,X3),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( X1 = k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))
    | r2_hidden(esk1_3(esk4_0,k2_tops_1(esk3_0,esk4_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_36])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk4_0,X1) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)
    | r2_hidden(esk1_3(esk4_0,X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_51])).

cnf(c_0_75,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_tops_1(X2,X1)))) = k1_tops_1(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_39])).

cnf(c_0_77,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_74])).

cnf(c_0_79,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_75,c_0_17])).

cnf(c_0_80,plain,
    ( k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,X2))) = k5_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_47])).

fof(c_0_81,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | k2_tops_1(X33,X34) = k7_subset_1(u1_struct_0(X33),k2_pre_topc(X33,X34),k1_tops_1(X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_82,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_53]),c_0_51])])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_28]),c_0_28])).

cnf(c_0_85,plain,
    ( k1_setfam_1(k2_tarski(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0))) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_69]),c_0_69])).

cnf(c_0_86,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | k1_tops_1(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_51]),c_0_53])])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_83])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_72])).

cnf(c_0_90,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_91,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_65]),c_0_53]),c_0_51])]),c_0_55])).

cnf(c_0_92,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k1_tops_1(esk3_0,esk4_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_93,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:56:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.28/5.51  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 5.28/5.51  # and selection function SelectMaxLComplexAvoidPosPred.
% 5.28/5.51  #
% 5.28/5.51  # Preprocessing time       : 0.028 s
% 5.28/5.51  
% 5.28/5.51  # Proof found!
% 5.28/5.51  # SZS status Theorem
% 5.28/5.51  # SZS output start CNFRefutation
% 5.28/5.51  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.28/5.51  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.28/5.51  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.28/5.51  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.28/5.51  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.28/5.51  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.28/5.51  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 5.28/5.51  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 5.28/5.51  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.28/5.51  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.28/5.51  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.28/5.51  fof(c_0_11, plain, ![X24, X25]:k4_xboole_0(X24,X25)=k5_xboole_0(X24,k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 5.28/5.51  fof(c_0_12, plain, ![X29, X30]:k1_setfam_1(k2_tarski(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 5.28/5.51  fof(c_0_13, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k4_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k4_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 5.28/5.51  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.28/5.51  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.28/5.51  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.28/5.51  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 5.28/5.51  fof(c_0_18, plain, ![X23]:k3_xboole_0(X23,X23)=X23, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 5.28/5.51  cnf(c_0_19, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.28/5.51  cnf(c_0_20, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 5.28/5.51  cnf(c_0_21, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.28/5.51  cnf(c_0_22, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 5.28/5.51  fof(c_0_23, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 5.28/5.51  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.28/5.51  fof(c_0_25, plain, ![X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k7_subset_1(X26,X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 5.28/5.51  cnf(c_0_26, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_20])).
% 5.28/5.51  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_21, c_0_15])).
% 5.28/5.51  cnf(c_0_28, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_22])).
% 5.28/5.51  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.28/5.51  cnf(c_0_30, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.28/5.51  cnf(c_0_31, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_24, c_0_17])).
% 5.28/5.51  cnf(c_0_32, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.28/5.51  cnf(c_0_33, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 5.28/5.51  cnf(c_0_34, plain, (k5_xboole_0(X1,X1)=X1|r2_hidden(esk2_3(X1,X1,X1),X1)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 5.28/5.51  cnf(c_0_35, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_29, c_0_15])).
% 5.28/5.51  cnf(c_0_36, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_30, c_0_15])).
% 5.28/5.51  fof(c_0_37, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 5.28/5.51  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))), inference(er,[status(thm)],[c_0_31])).
% 5.28/5.51  cnf(c_0_39, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_32, c_0_17])).
% 5.28/5.51  cnf(c_0_40, plain, (r2_hidden(esk2_3(X1,X1,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 5.28/5.51  cnf(c_0_41, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_35])).
% 5.28/5.51  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_36])).
% 5.28/5.51  fof(c_0_43, plain, ![X35, X36, X37, X38]:((~v3_pre_topc(X38,X36)|k1_tops_1(X36,X38)=X38|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X36)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(k1_tops_1(X35,X37)!=X37|v3_pre_topc(X37,X35)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X36)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 5.28/5.51  fof(c_0_44, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 5.28/5.51  cnf(c_0_45, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_27]), c_0_33])).
% 5.28/5.51  cnf(c_0_46, plain, (k7_subset_1(X1,X2,X2)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_27])).
% 5.28/5.51  cnf(c_0_47, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk2_3(X2,X2,X2),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 5.28/5.51  cnf(c_0_48, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|r2_hidden(esk2_3(X1,X1,X1),X1)), inference(spm,[status(thm)],[c_0_40, c_0_42])).
% 5.28/5.51  fof(c_0_49, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|k1_tops_1(X39,X40)=k7_subset_1(u1_struct_0(X39),X40,k2_tops_1(X39,X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 5.28/5.51  cnf(c_0_50, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.28/5.51  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 5.28/5.51  cnf(c_0_52, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 5.28/5.51  cnf(c_0_53, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 5.28/5.51  cnf(c_0_54, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k7_subset_1(X2,X1,X4))|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 5.28/5.51  cnf(c_0_55, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 5.28/5.51  fof(c_0_56, plain, ![X31, X32]:(~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|m1_subset_1(k2_pre_topc(X31,X32),k1_zfmisc_1(u1_struct_0(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 5.28/5.51  cnf(c_0_57, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k7_subset_1(X2,X1,X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 5.28/5.51  cnf(c_0_58, plain, (X1=X2|r2_hidden(esk2_3(X1,X1,X1),X1)|r2_hidden(esk2_3(X2,X2,X2),X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 5.28/5.51  cnf(c_0_59, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 5.28/5.51  cnf(c_0_60, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])])).
% 5.28/5.51  cnf(c_0_61, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,k2_tops_1(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 5.28/5.51  cnf(c_0_62, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 5.28/5.51  cnf(c_0_63, plain, (k7_subset_1(X1,X2,X2)=X3|r2_hidden(esk2_3(X3,X3,X3),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 5.28/5.51  cnf(c_0_64, plain, (~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,k1_tops_1(X1,X2))|~r2_hidden(X3,k2_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_54, c_0_59])).
% 5.28/5.51  cnf(c_0_65, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_51]), c_0_53])])).
% 5.28/5.51  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,k2_tops_1(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_53]), c_0_51])])).
% 5.28/5.51  cnf(c_0_67, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)=X1|r2_hidden(esk2_3(X1,X1,X1),X1)), inference(spm,[status(thm)],[c_0_63, c_0_51])).
% 5.28/5.51  cnf(c_0_68, negated_conjecture, (~r2_hidden(X1,k2_tops_1(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_53]), c_0_51])]), c_0_66])).
% 5.28/5.51  cnf(c_0_69, negated_conjecture, (k5_xboole_0(X1,X1)=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_67])).
% 5.28/5.51  cnf(c_0_70, negated_conjecture, (X1=k1_setfam_1(k2_tarski(X2,k2_tops_1(esk3_0,esk4_0)))|r2_hidden(esk1_3(X2,k2_tops_1(esk3_0,esk4_0),X1),X1)|~r2_hidden(esk1_3(X2,k2_tops_1(esk3_0,esk4_0),X1),esk4_0)), inference(spm,[status(thm)],[c_0_68, c_0_35])).
% 5.28/5.51  cnf(c_0_71, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,X3)|r2_hidden(esk1_3(X2,X3,X3),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 5.28/5.51  cnf(c_0_72, plain, (~r2_hidden(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0))), inference(rw,[status(thm)],[c_0_45, c_0_69])).
% 5.28/5.51  cnf(c_0_73, negated_conjecture, (X1=k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))|r2_hidden(esk1_3(esk4_0,k2_tops_1(esk3_0,esk4_0),X1),X1)), inference(spm,[status(thm)],[c_0_70, c_0_36])).
% 5.28/5.51  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk4_0,X1)=k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)|r2_hidden(esk1_3(esk4_0,X1,X1),X1)), inference(spm,[status(thm)],[c_0_71, c_0_51])).
% 5.28/5.51  cnf(c_0_75, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.28/5.51  cnf(c_0_76, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_tops_1(X2,X1))))=k1_tops_1(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_59, c_0_39])).
% 5.28/5.51  cnf(c_0_77, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 5.28/5.51  cnf(c_0_78, negated_conjecture, (k5_xboole_0(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_72, c_0_74])).
% 5.28/5.51  cnf(c_0_79, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_75, c_0_17])).
% 5.28/5.51  cnf(c_0_80, plain, (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,X2)))=k5_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_45, c_0_47])).
% 5.28/5.51  fof(c_0_81, plain, ![X33, X34]:(~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|k2_tops_1(X33,X34)=k7_subset_1(u1_struct_0(X33),k2_pre_topc(X33,X34),k1_tops_1(X33,X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 5.28/5.51  cnf(c_0_82, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.28/5.51  cnf(c_0_83, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_53]), c_0_51])])).
% 5.28/5.51  cnf(c_0_84, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_28]), c_0_28])).
% 5.28/5.51  cnf(c_0_85, plain, (k1_setfam_1(k2_tarski(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_69]), c_0_69])).
% 5.28/5.51  cnf(c_0_86, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 5.28/5.51  cnf(c_0_87, negated_conjecture, (v3_pre_topc(X1,X2)|k1_tops_1(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_51]), c_0_53])])).
% 5.28/5.51  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_78, c_0_83])).
% 5.28/5.51  cnf(c_0_89, plain, (k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_72])).
% 5.28/5.51  cnf(c_0_90, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 5.28/5.51  cnf(c_0_91, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_65]), c_0_53]), c_0_51])]), c_0_55])).
% 5.28/5.51  cnf(c_0_92, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k1_tops_1(esk3_0,esk4_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_51]), c_0_52]), c_0_53])])).
% 5.28/5.51  cnf(c_0_93, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[c_0_88, c_0_89])).
% 5.28/5.51  cnf(c_0_94, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 5.28/5.51  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])]), c_0_94]), ['proof']).
% 5.28/5.51  # SZS output end CNFRefutation
% 5.28/5.51  # Proof object total steps             : 96
% 5.28/5.51  # Proof object clause steps            : 73
% 5.28/5.51  # Proof object formula steps           : 23
% 5.28/5.51  # Proof object conjectures             : 28
% 5.28/5.51  # Proof object clause conjectures      : 25
% 5.28/5.51  # Proof object formula conjectures     : 3
% 5.28/5.51  # Proof object initial clauses used    : 20
% 5.28/5.51  # Proof object initial formulas used   : 11
% 5.28/5.51  # Proof object generating inferences   : 36
% 5.28/5.51  # Proof object simplifying inferences  : 49
% 5.28/5.51  # Training examples: 0 positive, 0 negative
% 5.28/5.51  # Parsed axioms                        : 11
% 5.28/5.51  # Removed by relevancy pruning/SinE    : 0
% 5.28/5.51  # Initial clauses                      : 26
% 5.28/5.51  # Removed in clause preprocessing      : 2
% 5.28/5.51  # Initial clauses in saturation        : 24
% 5.28/5.51  # Processed clauses                    : 6529
% 5.28/5.51  # ...of these trivial                  : 18
% 5.28/5.51  # ...subsumed                          : 5398
% 5.28/5.51  # ...remaining for further processing  : 1113
% 5.28/5.51  # Other redundant clauses eliminated   : 39
% 5.28/5.51  # Clauses deleted for lack of memory   : 0
% 5.28/5.51  # Backward-subsumed                    : 107
% 5.28/5.51  # Backward-rewritten                   : 139
% 5.28/5.51  # Generated clauses                    : 396178
% 5.28/5.51  # ...of the previous two non-trivial   : 386951
% 5.28/5.51  # Contextual simplify-reflections      : 18
% 5.28/5.51  # Paramodulations                      : 395423
% 5.28/5.51  # Factorizations                       : 716
% 5.28/5.51  # Equation resolutions                 : 39
% 5.28/5.51  # Propositional unsat checks           : 0
% 5.28/5.51  #    Propositional check models        : 0
% 5.28/5.51  #    Propositional check unsatisfiable : 0
% 5.28/5.51  #    Propositional clauses             : 0
% 5.28/5.51  #    Propositional clauses after purity: 0
% 5.28/5.51  #    Propositional unsat core size     : 0
% 5.28/5.51  #    Propositional preprocessing time  : 0.000
% 5.28/5.51  #    Propositional encoding time       : 0.000
% 5.28/5.51  #    Propositional solver time         : 0.000
% 5.28/5.51  #    Success case prop preproc time    : 0.000
% 5.28/5.51  #    Success case prop encoding time   : 0.000
% 5.28/5.51  #    Success case prop solver time     : 0.000
% 5.28/5.51  # Current number of processed clauses  : 861
% 5.28/5.51  #    Positive orientable unit clauses  : 25
% 5.28/5.51  #    Positive unorientable unit clauses: 0
% 5.28/5.51  #    Negative unit clauses             : 2
% 5.28/5.51  #    Non-unit-clauses                  : 834
% 5.28/5.51  # Current number of unprocessed clauses: 379149
% 5.28/5.51  # ...number of literals in the above   : 1986268
% 5.28/5.51  # Current number of archived formulas  : 0
% 5.28/5.51  # Current number of archived clauses   : 248
% 5.28/5.51  # Clause-clause subsumption calls (NU) : 142262
% 5.28/5.51  # Rec. Clause-clause subsumption calls : 69838
% 5.28/5.51  # Non-unit clause-clause subsumptions  : 5088
% 5.28/5.51  # Unit Clause-clause subsumption calls : 1684
% 5.28/5.51  # Rewrite failures with RHS unbound    : 32
% 5.28/5.51  # BW rewrite match attempts            : 85
% 5.28/5.51  # BW rewrite match successes           : 20
% 5.28/5.51  # Condensation attempts                : 0
% 5.28/5.51  # Condensation successes               : 0
% 5.28/5.51  # Termbank termtop insertions          : 9037876
% 5.28/5.52  
% 5.28/5.52  # -------------------------------------------------
% 5.28/5.52  # User time                : 4.993 s
% 5.28/5.52  # System time              : 0.165 s
% 5.28/5.52  # Total time               : 5.158 s
% 5.28/5.52  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
