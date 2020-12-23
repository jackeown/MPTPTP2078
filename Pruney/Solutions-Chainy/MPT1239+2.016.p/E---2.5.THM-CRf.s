%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:55 EST 2020

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 266 expanded)
%              Number of clauses        :   63 ( 128 expanded)
%              Number of leaves         :   12 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  207 ( 719 expanded)
%              Number of equality atoms :   28 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t64_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tops_1])).

fof(c_0_13,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | r1_tarski(k1_tops_1(X29,X30),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_xboole_0(X21,X23)
      | r1_tarski(X21,k4_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_18,plain,(
    ! [X7,X8,X9] :
      ( ( r1_tarski(X7,X8)
        | ~ r1_tarski(X7,k4_xboole_0(X8,X9)) )
      & ( r1_xboole_0(X7,X9)
        | ~ r1_tarski(X7,k4_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X19,X20)
      | ~ r1_xboole_0(X18,X20)
      | r1_xboole_0(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).

fof(c_0_27,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(k2_xboole_0(X10,X11),X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k4_xboole_0(X4,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,esk2_0),esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_36,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X3,k4_xboole_0(X4,X5))
    | ~ r1_tarski(X2,X5)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_24])).

fof(c_0_40,plain,(
    ! [X31,X32,X33] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ r1_tarski(X32,X33)
      | r1_tarski(k1_tops_1(X31,X32),k1_tops_1(X31,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | ~ r1_tarski(k4_xboole_0(X3,X2),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X4,k4_xboole_0(X5,X6))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X6)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_23,c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_41])).

fof(c_0_49,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k7_subset_1(X24,X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_50,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,esk2_0),X1) = X1
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X2)
    | ~ r1_tarski(k4_xboole_0(X3,X2),X1)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k4_xboole_0(X4,X5))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X5) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_16])).

cnf(c_0_56,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_48])).

cnf(c_0_57,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X3)
    | ~ r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_31])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_22])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X3) = X3
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_22])).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_41])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_58])).

cnf(c_0_73,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1) = k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k1_tops_1(esk1_0,esk3_0)),esk3_0) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0)
    | ~ r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),X2)
    | ~ r1_tarski(u1_struct_0(esk1_0),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(X1,k4_xboole_0(X2,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_58])).

cnf(c_0_82,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_41]),c_0_31])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X2))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X2),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_73])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.32/1.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 1.32/1.51  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 1.32/1.51  #
% 1.32/1.51  # Preprocessing time       : 0.028 s
% 1.32/1.51  # Presaturation interreduction done
% 1.32/1.51  
% 1.32/1.51  # Proof found!
% 1.32/1.51  # SZS status Theorem
% 1.32/1.51  # SZS output start CNFRefutation
% 1.32/1.51  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tops_1)).
% 1.32/1.51  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 1.32/1.51  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 1.32/1.51  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.32/1.51  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.32/1.51  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.32/1.51  fof(t64_xboole_1, axiom, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&r1_tarski(X3,X4))&r1_xboole_0(X2,X4))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 1.32/1.51  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.32/1.51  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.32/1.51  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.32/1.51  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 1.32/1.51  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.32/1.51  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 1.32/1.51  fof(c_0_13, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|r1_tarski(k1_tops_1(X29,X30),X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 1.32/1.51  fof(c_0_14, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 1.32/1.51  cnf(c_0_15, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.32/1.51  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.32/1.51  fof(c_0_17, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_xboole_0(X21,X23)|r1_tarski(X21,k4_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 1.32/1.51  fof(c_0_18, plain, ![X7, X8, X9]:((r1_tarski(X7,X8)|~r1_tarski(X7,k4_xboole_0(X8,X9)))&(r1_xboole_0(X7,X9)|~r1_tarski(X7,k4_xboole_0(X8,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 1.32/1.51  fof(c_0_19, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.32/1.51  fof(c_0_20, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.32/1.51  cnf(c_0_21, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.32/1.51  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.32/1.51  cnf(c_0_23, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.32/1.51  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.32/1.51  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.32/1.51  fof(c_0_26, plain, ![X17, X18, X19, X20]:(~r1_tarski(X17,X18)|~r1_tarski(X19,X20)|~r1_xboole_0(X18,X20)|r1_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).
% 1.32/1.51  fof(c_0_27, plain, ![X10, X11, X12]:(~r1_tarski(k2_xboole_0(X10,X11),X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 1.32/1.51  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.32/1.51  cnf(c_0_29, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.32/1.51  cnf(c_0_30, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,k4_xboole_0(X4,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.32/1.51  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 1.32/1.51  cnf(c_0_32, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)|~r1_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.32/1.51  fof(c_0_33, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.32/1.51  cnf(c_0_34, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.32/1.51  cnf(c_0_35, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,esk2_0),esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.32/1.51  fof(c_0_36, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.32/1.51  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.32/1.51  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.32/1.51  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X3,k4_xboole_0(X4,X5))|~r1_tarski(X2,X5)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_32, c_0_24])).
% 1.32/1.51  fof(c_0_40, plain, ![X31, X32, X33]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|(~r1_tarski(X32,X33)|r1_tarski(k1_tops_1(X31,X32),k1_tops_1(X31,X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 1.32/1.51  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.32/1.51  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.32/1.51  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.32/1.51  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X2)|~r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))|~r1_tarski(k4_xboole_0(X3,X2),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.32/1.51  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.32/1.51  cnf(c_0_46, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X4,k4_xboole_0(X5,X6))|~r1_tarski(X1,X2)|~r1_tarski(X3,X6)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_23, c_0_39])).
% 1.32/1.51  cnf(c_0_47, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.32/1.51  cnf(c_0_48, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_28, c_0_41])).
% 1.32/1.51  fof(c_0_49, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k7_subset_1(X24,X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 1.32/1.51  cnf(c_0_50, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,esk2_0),X1)=X1|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_42])).
% 1.32/1.51  cnf(c_0_51, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_43, c_0_22])).
% 1.32/1.51  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X2)|~r1_tarski(k4_xboole_0(X3,X2),X1)|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 1.32/1.51  cnf(c_0_53, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_45, c_0_41])).
% 1.32/1.51  cnf(c_0_54, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,k4_xboole_0(X4,X5))|~r1_tarski(X1,X2)|~r1_tarski(X3,X5)), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 1.32/1.51  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_16])).
% 1.32/1.51  cnf(c_0_56, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_34, c_0_48])).
% 1.32/1.51  cnf(c_0_57, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.32/1.51  cnf(c_0_58, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.32/1.51  cnf(c_0_59, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 1.32/1.51  cnf(c_0_60, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.32/1.51  cnf(c_0_61, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X3)|~r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.32/1.51  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))|~r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_54, c_0_31])).
% 1.32/1.51  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.32/1.51  cnf(c_0_64, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_55, c_0_22])).
% 1.32/1.51  cnf(c_0_65, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X3)=X3|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_28, c_0_56])).
% 1.32/1.51  cnf(c_0_66, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.32/1.51  cnf(c_0_67, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_22])).
% 1.32/1.51  cnf(c_0_68, plain, (k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.32/1.51  cnf(c_0_69, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.32/1.51  cnf(c_0_70, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X3)|~r1_tarski(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_41])])).
% 1.32/1.51  cnf(c_0_71, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_63])).
% 1.32/1.51  cnf(c_0_72, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_58])).
% 1.32/1.51  cnf(c_0_73, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_65, c_0_51])).
% 1.32/1.51  cnf(c_0_74, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 1.32/1.51  cnf(c_0_75, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1)=k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.32/1.51  cnf(c_0_76, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k1_tops_1(esk1_0,esk3_0)),esk3_0)=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.32/1.51  cnf(c_0_77, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)|~r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_72])).
% 1.32/1.51  cnf(c_0_78, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),X2)|~r1_tarski(u1_struct_0(esk1_0),X2)), inference(spm,[status(thm)],[c_0_34, c_0_73])).
% 1.32/1.51  cnf(c_0_79, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 1.32/1.51  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(X1,k4_xboole_0(X2,esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_76])).
% 1.32/1.51  cnf(c_0_81, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_21, c_0_58])).
% 1.32/1.51  cnf(c_0_82, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_41]), c_0_31])])).
% 1.32/1.51  cnf(c_0_83, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 1.32/1.51  cnf(c_0_84, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X2))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),X3)|~r1_tarski(k4_xboole_0(X1,X2),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_30, c_0_81])).
% 1.32/1.51  cnf(c_0_85, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_82])).
% 1.32/1.51  cnf(c_0_86, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_59, c_0_73])).
% 1.32/1.51  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_86])]), ['proof']).
% 1.32/1.51  # SZS output end CNFRefutation
% 1.32/1.51  # Proof object total steps             : 88
% 1.32/1.51  # Proof object clause steps            : 63
% 1.32/1.51  # Proof object formula steps           : 25
% 1.32/1.51  # Proof object conjectures             : 35
% 1.32/1.51  # Proof object clause conjectures      : 32
% 1.32/1.51  # Proof object formula conjectures     : 3
% 1.32/1.51  # Proof object initial clauses used    : 18
% 1.32/1.51  # Proof object initial formulas used   : 12
% 1.32/1.51  # Proof object generating inferences   : 42
% 1.32/1.51  # Proof object simplifying inferences  : 11
% 1.32/1.51  # Training examples: 0 positive, 0 negative
% 1.32/1.51  # Parsed axioms                        : 12
% 1.32/1.51  # Removed by relevancy pruning/SinE    : 0
% 1.32/1.51  # Initial clauses                      : 20
% 1.32/1.51  # Removed in clause preprocessing      : 0
% 1.32/1.51  # Initial clauses in saturation        : 20
% 1.32/1.51  # Processed clauses                    : 12673
% 1.32/1.51  # ...of these trivial                  : 578
% 1.32/1.51  # ...subsumed                          : 8344
% 1.32/1.51  # ...remaining for further processing  : 3751
% 1.32/1.51  # Other redundant clauses eliminated   : 2
% 1.32/1.51  # Clauses deleted for lack of memory   : 0
% 1.32/1.51  # Backward-subsumed                    : 130
% 1.32/1.51  # Backward-rewritten                   : 29
% 1.32/1.51  # Generated clauses                    : 103081
% 1.32/1.51  # ...of the previous two non-trivial   : 89914
% 1.32/1.51  # Contextual simplify-reflections      : 2
% 1.32/1.51  # Paramodulations                      : 103079
% 1.32/1.51  # Factorizations                       : 0
% 1.32/1.51  # Equation resolutions                 : 2
% 1.32/1.51  # Propositional unsat checks           : 0
% 1.32/1.51  #    Propositional check models        : 0
% 1.32/1.51  #    Propositional check unsatisfiable : 0
% 1.32/1.51  #    Propositional clauses             : 0
% 1.32/1.51  #    Propositional clauses after purity: 0
% 1.32/1.51  #    Propositional unsat core size     : 0
% 1.32/1.51  #    Propositional preprocessing time  : 0.000
% 1.32/1.51  #    Propositional encoding time       : 0.000
% 1.32/1.51  #    Propositional solver time         : 0.000
% 1.32/1.51  #    Success case prop preproc time    : 0.000
% 1.32/1.51  #    Success case prop encoding time   : 0.000
% 1.32/1.51  #    Success case prop solver time     : 0.000
% 1.32/1.51  # Current number of processed clauses  : 3571
% 1.32/1.51  #    Positive orientable unit clauses  : 784
% 1.32/1.51  #    Positive unorientable unit clauses: 0
% 1.32/1.51  #    Negative unit clauses             : 128
% 1.32/1.51  #    Non-unit-clauses                  : 2659
% 1.32/1.51  # Current number of unprocessed clauses: 77231
% 1.32/1.51  # ...number of literals in the above   : 157195
% 1.32/1.51  # Current number of archived formulas  : 0
% 1.32/1.51  # Current number of archived clauses   : 178
% 1.32/1.51  # Clause-clause subsumption calls (NU) : 1022328
% 1.32/1.51  # Rec. Clause-clause subsumption calls : 991185
% 1.32/1.51  # Non-unit clause-clause subsumptions  : 4850
% 1.32/1.51  # Unit Clause-clause subsumption calls : 52739
% 1.32/1.51  # Rewrite failures with RHS unbound    : 0
% 1.32/1.51  # BW rewrite match attempts            : 2396
% 1.32/1.51  # BW rewrite match successes           : 20
% 1.32/1.51  # Condensation attempts                : 0
% 1.32/1.51  # Condensation successes               : 0
% 1.32/1.51  # Termbank termtop insertions          : 1839984
% 1.32/1.51  
% 1.32/1.51  # -------------------------------------------------
% 1.32/1.51  # User time                : 1.121 s
% 1.32/1.51  # System time              : 0.049 s
% 1.32/1.51  # Total time               : 1.171 s
% 1.32/1.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
