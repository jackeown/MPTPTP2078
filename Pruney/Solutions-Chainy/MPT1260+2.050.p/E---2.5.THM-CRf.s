%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:22 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  108 (3085 expanded)
%              Number of clauses        :   81 (1507 expanded)
%              Number of leaves         :   13 ( 762 expanded)
%              Depth                    :   25
%              Number of atoms          :  293 (6830 expanded)
%              Number of equality atoms :  108 (3433 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

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

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_13,plain,(
    ! [X27,X28] : k4_xboole_0(X27,X28) = k5_xboole_0(X27,k3_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X36,X37] : k1_setfam_1(k2_tarski(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | k3_xboole_0(X29,X30) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_22,plain,(
    ! [X25,X26] :
      ( ( r1_tarski(X25,X26)
        | X25 != X26 )
      & ( r1_tarski(X26,X25)
        | X25 != X26 )
      & ( ~ r1_tarski(X25,X26)
        | ~ r1_tarski(X26,X25)
        | X25 = X26 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_23,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k7_subset_1(X33,X34,X35) = k4_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_33,plain,(
    ! [X31,X32] : k4_xboole_0(X31,k4_xboole_0(X31,X32)) = k3_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_34,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_42,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_17]),c_0_19]),c_0_19])).

cnf(c_0_45,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,k5_xboole_0(X2,X2)))
    | r2_hidden(esk1_3(X2,k5_xboole_0(X2,X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_44])).

cnf(c_0_49,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,k5_xboole_0(X2,X2)))
    | ~ r2_hidden(esk1_3(X2,k5_xboole_0(X2,X2),X1),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_45])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_35])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_46,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_53,plain,
    ( k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X1))) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_35]),c_0_35])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,X1) = k1_setfam_1(k2_tarski(X2,k5_xboole_0(X2,X2)))
    | ~ r2_hidden(esk1_3(X2,k5_xboole_0(X2,X2),k5_xboole_0(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( X1 = k1_setfam_1(k2_tarski(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)))
    | r2_hidden(esk1_3(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0))) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(X2,X2)
    | ~ r2_hidden(esk1_3(X2,k5_xboole_0(X2,X2),k5_xboole_0(X1,X1)),X1) ),
    inference(rw,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_61,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_19])).

cnf(c_0_62,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_56,c_0_19])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)
    | r2_hidden(esk1_3(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0),X1),X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(X1,X1) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)
    | ~ r2_hidden(esk1_3(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0),k5_xboole_0(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_52])).

cnf(c_0_66,plain,
    ( X1 = k5_xboole_0(X2,X2)
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(X1,X1) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_47])).

cnf(c_0_69,plain,
    ( X1 = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

fof(c_0_70,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | m1_subset_1(k2_pre_topc(X38,X39),k1_zfmisc_1(u1_struct_0(X38))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_71,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)
    | r2_hidden(esk2_3(X2,X2,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)) = k1_setfam_1(k2_tarski(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_47]),c_0_47])).

cnf(c_0_73,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_76,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,X1)) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)
    | r2_hidden(esk2_3(X2,X2,k1_setfam_1(k2_tarski(esk4_0,X1))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_43]),c_0_74])])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_75,c_0_17])).

fof(c_0_79,plain,(
    ! [X42,X43,X44,X45] :
      ( ( ~ v3_pre_topc(X45,X43)
        | k1_tops_1(X43,X45) = X45
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ l1_pre_topc(X43)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( k1_tops_1(X42,X44) != X44
        | v3_pre_topc(X44,X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ l1_pre_topc(X43)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_80,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,X1)) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)
    | ~ r2_hidden(esk2_3(X2,X2,k1_setfam_1(k2_tarski(esk4_0,X1))),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk3_0,esk4_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk3_0,esk4_0),X1))) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_77])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_83,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_85,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,X1)) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)
    | ~ r2_hidden(esk2_3(X2,X2,k1_setfam_1(k2_tarski(esk4_0,X1))),k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)
    | r2_hidden(esk2_3(X3,X3,k1_setfam_1(k2_tarski(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_69])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_50,c_0_53])).

cnf(c_0_88,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_43]),c_0_84]),c_0_74])])).

fof(c_0_89,plain,(
    ! [X46,X47] :
      ( ~ l1_pre_topc(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | k1_tops_1(X46,X47) = k7_subset_1(u1_struct_0(X46),X47,k2_tops_1(X46,X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

fof(c_0_90,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
      | k2_tops_1(X40,X41) = k7_subset_1(u1_struct_0(X40),k2_pre_topc(X40,X41),k1_tops_1(X40,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_91,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_87,c_0_67])).

cnf(c_0_93,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_43]),c_0_74])])).

cnf(c_0_94,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_95,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_96,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_91]),c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0)
    | k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_43]),c_0_74])])).

cnf(c_0_100,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0)) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_43]),c_0_74])])).

cnf(c_0_101,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])])).

cnf(c_0_102,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_103,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_104,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_105,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103])])).

cnf(c_0_106,negated_conjecture,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_101]),c_0_84]),c_0_74]),c_0_43])]),c_0_105])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_43]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.39/0.56  # and selection function SelectCQArNTNpEqFirst.
% 0.39/0.56  #
% 0.39/0.56  # Preprocessing time       : 0.029 s
% 0.39/0.56  # Presaturation interreduction done
% 0.39/0.56  
% 0.39/0.56  # Proof found!
% 0.39/0.56  # SZS status Theorem
% 0.39/0.56  # SZS output start CNFRefutation
% 0.39/0.56  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.39/0.56  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.39/0.56  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.39/0.56  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.39/0.56  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.39/0.56  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.56  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.39/0.56  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 0.39/0.56  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.39/0.56  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.39/0.56  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.39/0.56  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 0.39/0.56  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 0.39/0.56  fof(c_0_13, plain, ![X27, X28]:k4_xboole_0(X27,X28)=k5_xboole_0(X27,k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.39/0.56  fof(c_0_14, plain, ![X36, X37]:k1_setfam_1(k2_tarski(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.39/0.56  fof(c_0_15, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.39/0.56  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.56  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.56  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.56  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.39/0.56  fof(c_0_20, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.39/0.56  fof(c_0_21, plain, ![X29, X30]:(~r1_tarski(X29,X30)|k3_xboole_0(X29,X30)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.39/0.56  fof(c_0_22, plain, ![X25, X26]:(((r1_tarski(X25,X26)|X25!=X26)&(r1_tarski(X26,X25)|X25!=X26))&(~r1_tarski(X25,X26)|~r1_tarski(X26,X25)|X25=X26)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.56  cnf(c_0_23, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.39/0.56  cnf(c_0_24, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.39/0.56  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.39/0.56  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.56  cnf(c_0_27, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_23])).
% 0.39/0.56  cnf(c_0_28, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_24, c_0_17])).
% 0.39/0.56  cnf(c_0_29, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_17])).
% 0.39/0.56  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.39/0.56  fof(c_0_31, plain, ![X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k7_subset_1(X33,X34,X35)=k4_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.39/0.56  fof(c_0_32, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 0.39/0.56  fof(c_0_33, plain, ![X31, X32]:k4_xboole_0(X31,k4_xboole_0(X31,X32))=k3_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.39/0.56  cnf(c_0_34, plain, (X1=k1_setfam_1(k2_tarski(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2))))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.39/0.56  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.39/0.56  cnf(c_0_36, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.39/0.56  cnf(c_0_37, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.39/0.56  fof(c_0_38, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.39/0.56  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.56  cnf(c_0_40, plain, (X1=k1_setfam_1(k2_tarski(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.39/0.56  cnf(c_0_41, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_36, c_0_17])).
% 0.39/0.56  cnf(c_0_42, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_37, c_0_19])).
% 0.39/0.56  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.56  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_17]), c_0_19]), c_0_19])).
% 0.39/0.56  cnf(c_0_45, plain, (X1=k1_setfam_1(k2_tarski(X2,k5_xboole_0(X2,X2)))|r2_hidden(esk1_3(X2,k5_xboole_0(X2,X2),X1),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.39/0.56  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.56  cnf(c_0_47, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.39/0.56  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))), inference(spm,[status(thm)],[c_0_44, c_0_44])).
% 0.39/0.56  cnf(c_0_49, plain, (X1=k1_setfam_1(k2_tarski(X2,k5_xboole_0(X2,X2)))|~r2_hidden(esk1_3(X2,k5_xboole_0(X2,X2),X1),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1))))), inference(spm,[status(thm)],[c_0_27, c_0_45])).
% 0.39/0.56  cnf(c_0_50, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X1))))=X1), inference(spm,[status(thm)],[c_0_44, c_0_35])).
% 0.39/0.56  cnf(c_0_51, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_46, c_0_19])).
% 0.39/0.56  cnf(c_0_52, negated_conjecture, (k5_xboole_0(esk4_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_35])).
% 0.39/0.56  cnf(c_0_53, plain, (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X1)))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_35]), c_0_35])).
% 0.39/0.56  cnf(c_0_54, plain, (k5_xboole_0(X1,X1)=k1_setfam_1(k2_tarski(X2,k5_xboole_0(X2,X2)))|~r2_hidden(esk1_3(X2,k5_xboole_0(X2,X2),k5_xboole_0(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.39/0.56  cnf(c_0_55, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.56  cnf(c_0_56, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.56  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))), inference(er,[status(thm)],[c_0_51])).
% 0.39/0.56  cnf(c_0_58, negated_conjecture, (X1=k1_setfam_1(k2_tarski(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)))|r2_hidden(esk1_3(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0),X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_52])).
% 0.39/0.56  cnf(c_0_59, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_52])).
% 0.39/0.56  cnf(c_0_60, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(X2,X2)|~r2_hidden(esk1_3(X2,k5_xboole_0(X2,X2),k5_xboole_0(X1,X1)),X1)), inference(rw,[status(thm)],[c_0_54, c_0_53])).
% 0.39/0.56  cnf(c_0_61, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_55, c_0_19])).
% 0.39/0.56  cnf(c_0_62, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_56, c_0_19])).
% 0.39/0.56  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_57, c_0_35])).
% 0.39/0.56  cnf(c_0_64, negated_conjecture, (X1=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)|r2_hidden(esk1_3(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0),X1),X1)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.39/0.56  cnf(c_0_65, negated_conjecture, (k5_xboole_0(X1,X1)=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)|~r2_hidden(esk1_3(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0),k5_xboole_0(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_60, c_0_52])).
% 0.39/0.56  cnf(c_0_66, plain, (X1=k5_xboole_0(X2,X2)|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_35])).
% 0.39/0.56  cnf(c_0_67, negated_conjecture, (k5_xboole_0(X1,X1)=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.39/0.56  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X2))), inference(spm,[status(thm)],[c_0_57, c_0_47])).
% 0.39/0.56  cnf(c_0_69, plain, (X1=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.39/0.56  fof(c_0_70, plain, ![X38, X39]:(~l1_pre_topc(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|m1_subset_1(k2_pre_topc(X38,X39),k1_zfmisc_1(u1_struct_0(X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.39/0.56  cnf(c_0_71, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)|r2_hidden(esk2_3(X2,X2,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.39/0.56  cnf(c_0_72, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1))=k1_setfam_1(k2_tarski(esk4_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_47]), c_0_47])).
% 0.39/0.56  cnf(c_0_73, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.39/0.56  cnf(c_0_74, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.56  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.39/0.56  cnf(c_0_76, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,X1))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)|r2_hidden(esk2_3(X2,X2,k1_setfam_1(k2_tarski(esk4_0,X1))),esk4_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.39/0.56  cnf(c_0_77, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_43]), c_0_74])])).
% 0.39/0.56  cnf(c_0_78, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_75, c_0_17])).
% 0.39/0.56  fof(c_0_79, plain, ![X42, X43, X44, X45]:((~v3_pre_topc(X45,X43)|k1_tops_1(X43,X45)=X45|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X43)))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~l1_pre_topc(X43)|(~v2_pre_topc(X42)|~l1_pre_topc(X42)))&(k1_tops_1(X42,X44)!=X44|v3_pre_topc(X44,X42)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X43)))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~l1_pre_topc(X43)|(~v2_pre_topc(X42)|~l1_pre_topc(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.39/0.56  cnf(c_0_80, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,X1))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)|~r2_hidden(esk2_3(X2,X2,k1_setfam_1(k2_tarski(esk4_0,X1))),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,esk4_0))))), inference(spm,[status(thm)],[c_0_27, c_0_76])).
% 0.39/0.56  cnf(c_0_81, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk3_0,esk4_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk3_0,esk4_0),X1)))=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_77])).
% 0.39/0.56  cnf(c_0_82, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_78])).
% 0.39/0.56  cnf(c_0_83, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.39/0.56  cnf(c_0_84, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.56  cnf(c_0_85, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,X1))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)|~r2_hidden(esk2_3(X2,X2,k1_setfam_1(k2_tarski(esk4_0,X1))),k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.39/0.56  cnf(c_0_86, plain, (k1_setfam_1(k2_tarski(X1,X2))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)|r2_hidden(esk2_3(X3,X3,k1_setfam_1(k2_tarski(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_82, c_0_69])).
% 0.39/0.56  cnf(c_0_87, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_50, c_0_53])).
% 0.39/0.56  cnf(c_0_88, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_43]), c_0_84]), c_0_74])])).
% 0.39/0.56  fof(c_0_89, plain, ![X46, X47]:(~l1_pre_topc(X46)|(~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|k1_tops_1(X46,X47)=k7_subset_1(u1_struct_0(X46),X47,k2_tops_1(X46,X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.39/0.56  fof(c_0_90, plain, ![X40, X41]:(~l1_pre_topc(X40)|(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|k2_tops_1(X40,X41)=k7_subset_1(u1_struct_0(X40),k2_pre_topc(X40,X41),k1_tops_1(X40,X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.39/0.56  cnf(c_0_91, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.39/0.56  cnf(c_0_92, plain, (k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk3_0),esk4_0,esk4_0))=X1), inference(rw,[status(thm)],[c_0_87, c_0_67])).
% 0.39/0.56  cnf(c_0_93, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_43]), c_0_74])])).
% 0.39/0.56  cnf(c_0_94, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.56  cnf(c_0_95, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.39/0.56  cnf(c_0_96, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.39/0.56  cnf(c_0_97, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_91]), c_0_92])).
% 0.39/0.56  cnf(c_0_98, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)|k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.39/0.56  cnf(c_0_99, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_43]), c_0_74])])).
% 0.39/0.56  cnf(c_0_100, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0))=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_43]), c_0_74])])).
% 0.39/0.56  cnf(c_0_101, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])])).
% 0.39/0.56  cnf(c_0_102, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.56  cnf(c_0_103, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_100, c_0_101])).
% 0.39/0.56  cnf(c_0_104, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.39/0.56  cnf(c_0_105, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103])])).
% 0.39/0.56  cnf(c_0_106, negated_conjecture, (~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_101]), c_0_84]), c_0_74]), c_0_43])]), c_0_105])).
% 0.39/0.56  cnf(c_0_107, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_43]), c_0_74])]), ['proof']).
% 0.39/0.56  # SZS output end CNFRefutation
% 0.39/0.56  # Proof object total steps             : 108
% 0.39/0.56  # Proof object clause steps            : 81
% 0.39/0.56  # Proof object formula steps           : 27
% 0.39/0.56  # Proof object conjectures             : 35
% 0.39/0.56  # Proof object clause conjectures      : 32
% 0.39/0.56  # Proof object formula conjectures     : 3
% 0.39/0.56  # Proof object initial clauses used    : 23
% 0.39/0.56  # Proof object initial formulas used   : 13
% 0.39/0.56  # Proof object generating inferences   : 36
% 0.39/0.56  # Proof object simplifying inferences  : 50
% 0.39/0.56  # Training examples: 0 positive, 0 negative
% 0.39/0.56  # Parsed axioms                        : 14
% 0.39/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.56  # Initial clauses                      : 31
% 0.39/0.56  # Removed in clause preprocessing      : 2
% 0.39/0.56  # Initial clauses in saturation        : 29
% 0.39/0.56  # Processed clauses                    : 1527
% 0.39/0.56  # ...of these trivial                  : 29
% 0.39/0.56  # ...subsumed                          : 793
% 0.39/0.56  # ...remaining for further processing  : 705
% 0.39/0.56  # Other redundant clauses eliminated   : 8
% 0.39/0.56  # Clauses deleted for lack of memory   : 0
% 0.39/0.56  # Backward-subsumed                    : 70
% 0.39/0.56  # Backward-rewritten                   : 256
% 0.39/0.56  # Generated clauses                    : 8846
% 0.39/0.56  # ...of the previous two non-trivial   : 8827
% 0.39/0.56  # Contextual simplify-reflections      : 6
% 0.39/0.56  # Paramodulations                      : 8790
% 0.39/0.56  # Factorizations                       : 48
% 0.39/0.56  # Equation resolutions                 : 8
% 0.39/0.56  # Propositional unsat checks           : 0
% 0.39/0.56  #    Propositional check models        : 0
% 0.39/0.56  #    Propositional check unsatisfiable : 0
% 0.39/0.56  #    Propositional clauses             : 0
% 0.39/0.56  #    Propositional clauses after purity: 0
% 0.39/0.56  #    Propositional unsat core size     : 0
% 0.39/0.56  #    Propositional preprocessing time  : 0.000
% 0.39/0.56  #    Propositional encoding time       : 0.000
% 0.39/0.56  #    Propositional solver time         : 0.000
% 0.39/0.56  #    Success case prop preproc time    : 0.000
% 0.39/0.56  #    Success case prop encoding time   : 0.000
% 0.39/0.56  #    Success case prop solver time     : 0.000
% 0.39/0.56  # Current number of processed clauses  : 343
% 0.39/0.56  #    Positive orientable unit clauses  : 120
% 0.39/0.56  #    Positive unorientable unit clauses: 1
% 0.39/0.56  #    Negative unit clauses             : 1
% 0.39/0.56  #    Non-unit-clauses                  : 221
% 0.39/0.56  # Current number of unprocessed clauses: 7142
% 0.39/0.56  # ...number of literals in the above   : 19541
% 0.39/0.56  # Current number of archived formulas  : 0
% 0.39/0.56  # Current number of archived clauses   : 356
% 0.39/0.56  # Clause-clause subsumption calls (NU) : 18426
% 0.39/0.56  # Rec. Clause-clause subsumption calls : 16297
% 0.39/0.56  # Non-unit clause-clause subsumptions  : 865
% 0.39/0.56  # Unit Clause-clause subsumption calls : 474
% 0.39/0.56  # Rewrite failures with RHS unbound    : 0
% 0.39/0.56  # BW rewrite match attempts            : 2459
% 0.39/0.56  # BW rewrite match successes           : 42
% 0.39/0.56  # Condensation attempts                : 0
% 0.39/0.56  # Condensation successes               : 0
% 0.39/0.56  # Termbank termtop insertions          : 302731
% 0.39/0.56  
% 0.39/0.56  # -------------------------------------------------
% 0.39/0.56  # User time                : 0.204 s
% 0.39/0.56  # System time              : 0.013 s
% 0.39/0.56  # Total time               : 0.217 s
% 0.39/0.56  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
