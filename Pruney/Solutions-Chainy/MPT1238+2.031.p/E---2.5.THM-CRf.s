%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:52 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 284 expanded)
%              Number of clauses        :   55 ( 129 expanded)
%              Number of leaves         :   10 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  168 ( 791 expanded)
%              Number of equality atoms :   28 ( 111 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t49_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

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

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X9,X10] : r1_tarski(X9,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tops_1])).

cnf(c_0_13,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X13,X12)
      | r1_tarski(k2_xboole_0(X11,X13),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(X6,k2_xboole_0(X8,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | r1_tarski(k1_tops_1(X22,X23),X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk1_0),esk3_0) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk1_0),esk2_0) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_33])).

fof(c_0_37,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k4_subset_1(X17,X18,X19) = k2_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk1_0),X1) = u1_struct_0(esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_36])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_29])).

cnf(c_0_42,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk3_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk1_0),X1) = u1_struct_0(esk1_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_48,plain,
    ( k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_51,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ r1_tarski(X25,X26)
      | r1_tarski(k1_tops_1(X24,X25),k1_tops_1(X24,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_52,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | m1_subset_1(k4_subset_1(X14,X15,X16),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_53,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,esk3_0) = k2_xboole_0(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_21]),c_0_21])])).

cnf(c_0_55,plain,
    ( k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_28])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k1_tops_1(esk1_0,esk3_0)) = k2_xboole_0(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_23]),c_0_28])])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)) = k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_23]),c_0_71])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_28]),c_0_14])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_20]),c_0_73]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n023.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:36:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 1.76/1.94  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 1.76/1.94  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 1.76/1.94  #
% 1.76/1.94  # Preprocessing time       : 0.027 s
% 1.76/1.94  # Presaturation interreduction done
% 1.76/1.94  
% 1.76/1.94  # Proof found!
% 1.76/1.94  # SZS status Theorem
% 1.76/1.94  # SZS output start CNFRefutation
% 1.76/1.94  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.76/1.94  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.76/1.94  fof(t49_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tops_1)).
% 1.76/1.94  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.76/1.94  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.76/1.94  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.76/1.94  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.76/1.94  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.76/1.94  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 1.76/1.94  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 1.76/1.94  fof(c_0_10, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.76/1.94  fof(c_0_11, plain, ![X9, X10]:r1_tarski(X9,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.76/1.94  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t49_tops_1])).
% 1.76/1.94  cnf(c_0_13, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.76/1.94  cnf(c_0_14, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.76/1.94  fof(c_0_15, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X13,X12)|r1_tarski(k2_xboole_0(X11,X13),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.76/1.94  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.76/1.94  fof(c_0_17, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.76/1.94  fof(c_0_18, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 1.76/1.94  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 1.76/1.94  cnf(c_0_20, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.76/1.94  cnf(c_0_21, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 1.76/1.94  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.76/1.94  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.76/1.94  fof(c_0_24, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(X6,k2_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 1.76/1.94  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 1.76/1.94  cnf(c_0_26, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.76/1.94  fof(c_0_27, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|r1_tarski(k1_tops_1(X22,X23),X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 1.76/1.94  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.76/1.94  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.76/1.94  cnf(c_0_30, negated_conjecture, (k2_xboole_0(u1_struct_0(esk1_0),esk3_0)=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.76/1.94  cnf(c_0_31, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.76/1.94  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.76/1.94  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 1.76/1.94  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.76/1.94  cnf(c_0_35, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.76/1.94  cnf(c_0_36, negated_conjecture, (k2_xboole_0(u1_struct_0(esk1_0),esk2_0)=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_25, c_0_33])).
% 1.76/1.94  fof(c_0_37, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|~m1_subset_1(X19,k1_zfmisc_1(X17))|k4_subset_1(X17,X18,X19)=k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 1.76/1.95  cnf(c_0_38, negated_conjecture, (k2_xboole_0(u1_struct_0(esk1_0),X1)=u1_struct_0(esk1_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_34])).
% 1.76/1.95  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_23])).
% 1.76/1.95  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_36])).
% 1.76/1.95  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(k2_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_13, c_0_29])).
% 1.76/1.95  cnf(c_0_42, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.76/1.95  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.76/1.95  cnf(c_0_44, negated_conjecture, (k2_xboole_0(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk3_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.76/1.95  cnf(c_0_45, negated_conjecture, (k2_xboole_0(u1_struct_0(esk1_0),X1)=u1_struct_0(esk1_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_40])).
% 1.76/1.95  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_28])).
% 1.76/1.95  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(X3,X2)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_41, c_0_20])).
% 1.76/1.95  cnf(c_0_48, plain, (k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.76/1.95  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_44])).
% 1.76/1.95  cnf(c_0_50, negated_conjecture, (k2_xboole_0(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.76/1.95  fof(c_0_51, plain, ![X24, X25, X26]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~r1_tarski(X25,X26)|r1_tarski(k1_tops_1(X24,X25),k1_tops_1(X24,X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 1.76/1.95  fof(c_0_52, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|~m1_subset_1(X16,k1_zfmisc_1(X14))|m1_subset_1(k4_subset_1(X14,X15,X16),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 1.76/1.95  cnf(c_0_53, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,esk3_0)=k2_xboole_0(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 1.76/1.95  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_21]), c_0_21])])).
% 1.76/1.95  cnf(c_0_55, plain, (k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 1.76/1.95  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_49, c_0_21])).
% 1.76/1.95  cnf(c_0_57, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_50])).
% 1.76/1.95  cnf(c_0_58, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.76/1.95  cnf(c_0_59, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.76/1.95  cnf(c_0_60, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)=k2_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_28])).
% 1.76/1.95  cnf(c_0_61, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_54, c_0_29])).
% 1.76/1.95  cnf(c_0_62, negated_conjecture, (~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.76/1.95  cnf(c_0_63, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k1_tops_1(esk1_0,esk3_0))=k2_xboole_0(X1,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.76/1.95  cnf(c_0_64, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_57, c_0_21])).
% 1.76/1.95  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_32])).
% 1.76/1.95  cnf(c_0_66, negated_conjecture, (m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_23]), c_0_28])])).
% 1.76/1.95  cnf(c_0_67, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_61, c_0_21])).
% 1.76/1.95  cnf(c_0_68, negated_conjecture, (~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_62, c_0_60])).
% 1.76/1.95  cnf(c_0_69, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))=k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 1.76/1.95  cnf(c_0_70, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k2_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.76/1.95  cnf(c_0_71, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_14, c_0_67])).
% 1.76/1.95  cnf(c_0_72, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 1.76/1.95  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_23]), c_0_71])])).
% 1.76/1.95  cnf(c_0_74, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_28]), c_0_14])])).
% 1.76/1.95  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_20]), c_0_73]), c_0_74])]), ['proof']).
% 1.76/1.95  # SZS output end CNFRefutation
% 1.76/1.95  # Proof object total steps             : 76
% 1.76/1.95  # Proof object clause steps            : 55
% 1.76/1.95  # Proof object formula steps           : 21
% 1.76/1.95  # Proof object conjectures             : 36
% 1.76/1.95  # Proof object clause conjectures      : 33
% 1.76/1.95  # Proof object formula conjectures     : 3
% 1.76/1.95  # Proof object initial clauses used    : 15
% 1.76/1.95  # Proof object initial formulas used   : 10
% 1.76/1.95  # Proof object generating inferences   : 37
% 1.76/1.95  # Proof object simplifying inferences  : 17
% 1.76/1.95  # Training examples: 0 positive, 0 negative
% 1.76/1.95  # Parsed axioms                        : 10
% 1.76/1.95  # Removed by relevancy pruning/SinE    : 0
% 1.76/1.95  # Initial clauses                      : 16
% 1.76/1.95  # Removed in clause preprocessing      : 0
% 1.76/1.95  # Initial clauses in saturation        : 16
% 1.76/1.95  # Processed clauses                    : 16550
% 1.76/1.95  # ...of these trivial                  : 750
% 1.76/1.95  # ...subsumed                          : 12663
% 1.76/1.95  # ...remaining for further processing  : 3137
% 1.76/1.95  # Other redundant clauses eliminated   : 2
% 1.76/1.95  # Clauses deleted for lack of memory   : 0
% 1.76/1.95  # Backward-subsumed                    : 41
% 1.76/1.95  # Backward-rewritten                   : 390
% 1.76/1.95  # Generated clauses                    : 229089
% 1.76/1.95  # ...of the previous two non-trivial   : 193064
% 1.76/1.95  # Contextual simplify-reflections      : 0
% 1.76/1.95  # Paramodulations                      : 229087
% 1.76/1.95  # Factorizations                       : 0
% 1.76/1.95  # Equation resolutions                 : 2
% 1.76/1.95  # Propositional unsat checks           : 0
% 1.76/1.95  #    Propositional check models        : 0
% 1.76/1.95  #    Propositional check unsatisfiable : 0
% 1.76/1.95  #    Propositional clauses             : 0
% 1.76/1.95  #    Propositional clauses after purity: 0
% 1.76/1.95  #    Propositional unsat core size     : 0
% 1.76/1.95  #    Propositional preprocessing time  : 0.000
% 1.76/1.95  #    Propositional encoding time       : 0.000
% 1.76/1.95  #    Propositional solver time         : 0.000
% 1.76/1.95  #    Success case prop preproc time    : 0.000
% 1.76/1.95  #    Success case prop encoding time   : 0.000
% 1.76/1.95  #    Success case prop solver time     : 0.000
% 1.76/1.95  # Current number of processed clauses  : 2689
% 1.76/1.95  #    Positive orientable unit clauses  : 778
% 1.76/1.95  #    Positive unorientable unit clauses: 1
% 1.76/1.95  #    Negative unit clauses             : 1
% 1.76/1.95  #    Non-unit-clauses                  : 1909
% 1.76/1.95  # Current number of unprocessed clauses: 175114
% 1.76/1.95  # ...number of literals in the above   : 406159
% 1.76/1.95  # Current number of archived formulas  : 0
% 1.76/1.95  # Current number of archived clauses   : 446
% 1.76/1.95  # Clause-clause subsumption calls (NU) : 556950
% 1.76/1.95  # Rec. Clause-clause subsumption calls : 496087
% 1.76/1.95  # Non-unit clause-clause subsumptions  : 11526
% 1.76/1.95  # Unit Clause-clause subsumption calls : 43706
% 1.76/1.95  # Rewrite failures with RHS unbound    : 0
% 1.76/1.95  # BW rewrite match attempts            : 8781
% 1.76/1.95  # BW rewrite match successes           : 604
% 1.76/1.95  # Condensation attempts                : 0
% 1.76/1.95  # Condensation successes               : 0
% 1.76/1.95  # Termbank termtop insertions          : 4962464
% 1.76/1.95  
% 1.76/1.95  # -------------------------------------------------
% 1.76/1.95  # User time                : 1.549 s
% 1.76/1.95  # System time              : 0.076 s
% 1.76/1.95  # Total time               : 1.625 s
% 1.76/1.95  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
