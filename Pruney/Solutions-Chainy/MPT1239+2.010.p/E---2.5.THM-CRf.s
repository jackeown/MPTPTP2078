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
% DateTime   : Thu Dec  3 11:10:55 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 115 expanded)
%              Number of clauses        :   39 (  51 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 356 expanded)
%              Number of equality atoms :   11 (  14 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t64_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

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
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | m1_subset_1(k1_tops_1(X27,X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X18] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X17,X18)
      | ~ r1_xboole_0(X16,X18)
      | r1_xboole_0(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).

fof(c_0_19,plain,(
    ! [X7,X8,X9] :
      ( ( r1_tarski(X7,X8)
        | ~ r1_tarski(X7,k4_xboole_0(X8,X9)) )
      & ( r1_xboole_0(X7,X9)
        | ~ r1_tarski(X7,k4_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_20,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k7_subset_1(X22,X23,X24) = k4_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_xboole_0(X19,X21)
      | r1_tarski(X19,k4_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | r1_tarski(k1_tops_1(X29,X30),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_28,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X3,k4_xboole_0(X4,X5))
    | ~ r1_tarski(X2,X5)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X31,X32,X33] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ r1_tarski(X32,X33)
      | r1_tarski(k1_tops_1(X31,X32),k1_tops_1(X31,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X4,k4_xboole_0(X5,X6))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X6)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_17])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1) = k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k4_xboole_0(X4,X5))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X5) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_30])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X4))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X2),u1_struct_0(esk1_0))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

fof(c_0_55,plain,(
    ! [X13,X14] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(k4_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_30])).

cnf(c_0_58,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_59,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | r1_tarski(k4_xboole_0(X10,X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_61,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 0.21/0.52  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 0.21/0.52  #
% 0.21/0.52  # Preprocessing time       : 0.028 s
% 0.21/0.52  # Presaturation interreduction done
% 0.21/0.52  
% 0.21/0.52  # Proof found!
% 0.21/0.52  # SZS status Theorem
% 0.21/0.52  # SZS output start CNFRefutation
% 0.21/0.52  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 0.21/0.52  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.21/0.52  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.52  fof(t64_xboole_1, axiom, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&r1_tarski(X3,X4))&r1_xboole_0(X2,X4))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 0.21/0.52  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.21/0.52  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.21/0.52  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.21/0.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.52  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.21/0.52  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.21/0.52  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.52  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.21/0.52  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 0.21/0.52  fof(c_0_13, plain, ![X27, X28]:(~l1_pre_topc(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|m1_subset_1(k1_tops_1(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.21/0.52  fof(c_0_14, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.21/0.52  fof(c_0_15, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.52  cnf(c_0_16, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.52  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.52  fof(c_0_18, plain, ![X15, X16, X17, X18]:(~r1_tarski(X15,X16)|~r1_tarski(X17,X18)|~r1_xboole_0(X16,X18)|r1_xboole_0(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).
% 0.21/0.52  fof(c_0_19, plain, ![X7, X8, X9]:((r1_tarski(X7,X8)|~r1_tarski(X7,k4_xboole_0(X8,X9)))&(r1_xboole_0(X7,X9)|~r1_tarski(X7,k4_xboole_0(X8,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.21/0.52  fof(c_0_20, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k7_subset_1(X22,X23,X24)=k4_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.21/0.52  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.52  cnf(c_0_22, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.52  fof(c_0_23, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_xboole_0(X19,X21)|r1_tarski(X19,k4_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.21/0.52  cnf(c_0_24, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)|~r1_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.52  fof(c_0_26, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.52  fof(c_0_27, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|r1_tarski(k1_tops_1(X29,X30),X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.21/0.52  cnf(c_0_28, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.52  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.52  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.52  cnf(c_0_31, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.52  cnf(c_0_32, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.52  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X3,k4_xboole_0(X4,X5))|~r1_tarski(X2,X5)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.52  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.52  cnf(c_0_35, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.52  fof(c_0_36, plain, ![X31, X32, X33]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|(~r1_tarski(X32,X33)|r1_tarski(k1_tops_1(X31,X32),k1_tops_1(X31,X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.21/0.52  cnf(c_0_37, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.52  cnf(c_0_38, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.52  cnf(c_0_39, plain, (k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.21/0.52  cnf(c_0_40, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.21/0.52  cnf(c_0_41, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X4,k4_xboole_0(X5,X6))|~r1_tarski(X1,X2)|~r1_tarski(X3,X6)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.52  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.21/0.52  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_35, c_0_17])).
% 0.21/0.52  cnf(c_0_44, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.52  cnf(c_0_45, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.52  cnf(c_0_46, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1)=k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.52  cnf(c_0_47, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,k4_xboole_0(X4,X5))|~r1_tarski(X1,X2)|~r1_tarski(X3,X5)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.52  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_43, c_0_30])).
% 0.21/0.52  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.52  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_17])).
% 0.21/0.52  cnf(c_0_51, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.52  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X4))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),X3)|~r1_tarski(k4_xboole_0(X1,X2),u1_struct_0(esk1_0))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.52  cnf(c_0_53, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_49])).
% 0.21/0.52  cnf(c_0_54, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_29])).
% 0.21/0.52  fof(c_0_55, plain, ![X13, X14]:r1_tarski(k4_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.52  cnf(c_0_56, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))|~r1_tarski(k4_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.21/0.52  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_54, c_0_30])).
% 0.21/0.52  cnf(c_0_58, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.52  fof(c_0_59, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|r1_tarski(k4_xboole_0(X10,X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.21/0.52  cnf(c_0_60, negated_conjecture, (~r1_tarski(k4_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.21/0.52  cnf(c_0_61, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.52  cnf(c_0_62, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_21, c_0_29])).
% 0.21/0.52  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])]), ['proof']).
% 0.21/0.52  # SZS output end CNFRefutation
% 0.21/0.52  # Proof object total steps             : 64
% 0.21/0.52  # Proof object clause steps            : 39
% 0.21/0.52  # Proof object formula steps           : 25
% 0.21/0.52  # Proof object conjectures             : 25
% 0.21/0.52  # Proof object clause conjectures      : 22
% 0.21/0.52  # Proof object formula conjectures     : 3
% 0.21/0.52  # Proof object initial clauses used    : 16
% 0.21/0.52  # Proof object initial formulas used   : 12
% 0.21/0.52  # Proof object generating inferences   : 20
% 0.21/0.52  # Proof object simplifying inferences  : 9
% 0.21/0.52  # Training examples: 0 positive, 0 negative
% 0.21/0.52  # Parsed axioms                        : 12
% 0.21/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.52  # Initial clauses                      : 20
% 0.21/0.52  # Removed in clause preprocessing      : 0
% 0.21/0.52  # Initial clauses in saturation        : 20
% 0.21/0.52  # Processed clauses                    : 1175
% 0.21/0.52  # ...of these trivial                  : 46
% 0.21/0.52  # ...subsumed                          : 600
% 0.21/0.52  # ...remaining for further processing  : 529
% 0.21/0.52  # Other redundant clauses eliminated   : 2
% 0.21/0.52  # Clauses deleted for lack of memory   : 0
% 0.21/0.52  # Backward-subsumed                    : 0
% 0.21/0.52  # Backward-rewritten                   : 4
% 0.21/0.52  # Generated clauses                    : 10046
% 0.21/0.52  # ...of the previous two non-trivial   : 7361
% 0.21/0.52  # Contextual simplify-reflections      : 0
% 0.21/0.52  # Paramodulations                      : 10044
% 0.21/0.52  # Factorizations                       : 0
% 0.21/0.52  # Equation resolutions                 : 2
% 0.21/0.52  # Propositional unsat checks           : 0
% 0.21/0.52  #    Propositional check models        : 0
% 0.21/0.52  #    Propositional check unsatisfiable : 0
% 0.21/0.52  #    Propositional clauses             : 0
% 0.21/0.52  #    Propositional clauses after purity: 0
% 0.21/0.52  #    Propositional unsat core size     : 0
% 0.21/0.52  #    Propositional preprocessing time  : 0.000
% 0.21/0.52  #    Propositional encoding time       : 0.000
% 0.21/0.52  #    Propositional solver time         : 0.000
% 0.21/0.52  #    Success case prop preproc time    : 0.000
% 0.21/0.52  #    Success case prop encoding time   : 0.000
% 0.21/0.52  #    Success case prop solver time     : 0.000
% 0.21/0.52  # Current number of processed clauses  : 504
% 0.21/0.52  #    Positive orientable unit clauses  : 150
% 0.21/0.52  #    Positive unorientable unit clauses: 0
% 0.21/0.52  #    Negative unit clauses             : 2
% 0.21/0.52  #    Non-unit-clauses                  : 352
% 0.21/0.52  # Current number of unprocessed clauses: 6223
% 0.21/0.52  # ...number of literals in the above   : 15196
% 0.21/0.52  # Current number of archived formulas  : 0
% 0.21/0.52  # Current number of archived clauses   : 23
% 0.21/0.52  # Clause-clause subsumption calls (NU) : 14775
% 0.21/0.52  # Rec. Clause-clause subsumption calls : 13011
% 0.21/0.52  # Non-unit clause-clause subsumptions  : 600
% 0.21/0.52  # Unit Clause-clause subsumption calls : 989
% 0.21/0.52  # Rewrite failures with RHS unbound    : 0
% 0.21/0.52  # BW rewrite match attempts            : 667
% 0.21/0.52  # BW rewrite match successes           : 3
% 0.21/0.52  # Condensation attempts                : 0
% 0.21/0.52  # Condensation successes               : 0
% 0.21/0.52  # Termbank termtop insertions          : 203607
% 0.21/0.52  
% 0.21/0.52  # -------------------------------------------------
% 0.21/0.52  # User time                : 0.163 s
% 0.21/0.52  # System time              : 0.007 s
% 0.21/0.52  # Total time               : 0.170 s
% 0.21/0.52  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
