%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 412 expanded)
%              Number of clauses        :   62 ( 187 expanded)
%              Number of leaves         :   13 ( 102 expanded)
%              Depth                    :   24
%              Number of atoms          :  230 (1016 expanded)
%              Number of equality atoms :   11 ( 170 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

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

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(c_0_13,plain,(
    ! [X13,X14,X15] :
      ( ( r1_xboole_0(X13,k2_xboole_0(X14,X15))
        | ~ r1_xboole_0(X13,X14)
        | ~ r1_xboole_0(X13,X15) )
      & ( r1_xboole_0(X13,X14)
        | ~ r1_xboole_0(X13,k2_xboole_0(X14,X15)) )
      & ( r1_xboole_0(X13,X15)
        | ~ r1_xboole_0(X13,k2_xboole_0(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_15,plain,(
    ! [X16,X17] : r1_xboole_0(k4_xboole_0(X16,X17),X17) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_16,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k7_subset_1(X24,X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_20])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tops_1])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k7_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_30,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_xboole_0(X18,X20)
      | r1_tarski(X18,k4_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k7_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X4,X5)
    | ~ r1_tarski(X5,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_34,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_tarski(k5_xboole_0(X4,k3_xboole_0(X4,X3)),X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),k7_subset_1(u1_struct_0(esk1_0),esk3_0,X2))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X2),X1)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r1_tarski(k7_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32])])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_tarski(k5_xboole_0(X4,k3_xboole_0(X4,X3)),X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_49,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

fof(c_0_50,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),k7_subset_1(X1,esk3_0,X2))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_32])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k7_subset_1(X2,X3,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,X4)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

fof(c_0_55,plain,(
    ! [X31,X32,X33] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ r1_tarski(X32,X33)
      | r1_tarski(k1_tops_1(X31,X32),k1_tops_1(X31,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X4,X3)
    | ~ r1_xboole_0(X4,X2)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k7_subset_1(X1,X2,X3),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_44]),c_0_32])])).

cnf(c_0_65,negated_conjecture,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_42])])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ r1_xboole_0(k7_subset_1(X5,X4,X3),X2)
    | ~ r1_tarski(X1,k7_subset_1(X5,X4,X3)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_32])).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_subset_1(k7_subset_1(X1,esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(X1,esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_49]),c_0_42])]),c_0_44])).

fof(c_0_69,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | m1_subset_1(k1_tops_1(X27,X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_70,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | m1_subset_1(k7_subset_1(X21,X22,X23),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(X1,k2_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),esk3_0))
    | ~ r1_tarski(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_42])])).

fof(c_0_73,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | r1_tarski(k1_tops_1(X29,X30),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_74,negated_conjecture,
    ( ~ m1_subset_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_26])).

cnf(c_0_75,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r1_tarski(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_subset_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_61]),c_0_42])])).

cnf(c_0_80,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_26])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),esk3_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_42])])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_76]),c_0_61]),c_0_42])])).

cnf(c_0_84,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(X2,esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_42])])).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_78]),c_0_61]),c_0_32])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_42,c_0_87]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.56  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.56  #
% 0.20/0.56  # Preprocessing time       : 0.027 s
% 0.20/0.56  # Presaturation interreduction done
% 0.20/0.56  
% 0.20/0.56  # Proof found!
% 0.20/0.56  # SZS status Theorem
% 0.20/0.56  # SZS output start CNFRefutation
% 0.20/0.56  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.56  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.56  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.56  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.56  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.56  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tops_1)).
% 0.20/0.56  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.20/0.56  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.56  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.56  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.20/0.56  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.20/0.56  fof(dt_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 0.20/0.56  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.20/0.56  fof(c_0_13, plain, ![X13, X14, X15]:((r1_xboole_0(X13,k2_xboole_0(X14,X15))|~r1_xboole_0(X13,X14)|~r1_xboole_0(X13,X15))&((r1_xboole_0(X13,X14)|~r1_xboole_0(X13,k2_xboole_0(X14,X15)))&(r1_xboole_0(X13,X15)|~r1_xboole_0(X13,k2_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.56  fof(c_0_14, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.56  fof(c_0_15, plain, ![X16, X17]:r1_xboole_0(k4_xboole_0(X16,X17),X17), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.56  fof(c_0_16, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.56  cnf(c_0_17, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.56  cnf(c_0_19, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.56  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.56  fof(c_0_21, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k7_subset_1(X24,X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.56  cnf(c_0_22, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.56  cnf(c_0_23, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.56  cnf(c_0_24, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.56  cnf(c_0_25, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.56  cnf(c_0_26, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_24, c_0_20])).
% 0.20/0.56  fof(c_0_27, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 0.20/0.56  cnf(c_0_28, plain, (r1_xboole_0(k7_subset_1(X1,X2,X3),X4)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.56  fof(c_0_29, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.20/0.56  fof(c_0_30, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|~r1_xboole_0(X18,X20)|r1_tarski(X18,k4_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.20/0.56  cnf(c_0_31, plain, (r1_xboole_0(k7_subset_1(X1,X2,X3),X4)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X4,X5)|~r1_tarski(X5,X3)), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 0.20/0.56  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.56  cnf(c_0_33, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.56  fof(c_0_34, plain, ![X8, X9]:r1_tarski(k4_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.56  cnf(c_0_35, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),X2)|~r1_tarski(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.56  cnf(c_0_36, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[c_0_33, c_0_20])).
% 0.20/0.56  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.56  cnf(c_0_38, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),X2)|~r1_xboole_0(X2,X3)|~r1_tarski(k5_xboole_0(X4,k3_xboole_0(X4,X3)),X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.56  cnf(c_0_39, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_37, c_0_20])).
% 0.20/0.56  cnf(c_0_40, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),X2)|~r1_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.56  cnf(c_0_41, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_39])).
% 0.20/0.56  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.56  cnf(c_0_43, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1),k7_subset_1(u1_struct_0(esk1_0),esk3_0,X2))|~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk3_0,X2),X1)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.56  cnf(c_0_44, plain, (r1_tarski(k7_subset_1(X1,X2,X3),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 0.20/0.56  cnf(c_0_45, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),X2)|~r1_tarski(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_31, c_0_42])).
% 0.20/0.56  cnf(c_0_46, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1))|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_32])])).
% 0.20/0.56  cnf(c_0_47, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),X2)|~r1_xboole_0(X2,X3)|~r1_tarski(k5_xboole_0(X4,k3_xboole_0(X4,X3)),X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_45, c_0_36])).
% 0.20/0.56  cnf(c_0_48, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1))), inference(spm,[status(thm)],[c_0_46, c_0_39])).
% 0.20/0.56  cnf(c_0_49, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 0.20/0.56  fof(c_0_50, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_xboole_0(X11,X12)|r1_xboole_0(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.56  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),X2)|~r1_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_47, c_0_39])).
% 0.20/0.56  cnf(c_0_52, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),k7_subset_1(X1,esk3_0,X2))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_32])])).
% 0.20/0.56  cnf(c_0_53, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.56  cnf(c_0_54, plain, (r1_tarski(X1,k7_subset_1(X2,X3,X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X1,X4)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 0.20/0.56  fof(c_0_55, plain, ![X31, X32, X33]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|(~r1_tarski(X32,X33)|r1_tarski(k1_tops_1(X31,X32),k1_tops_1(X31,X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.20/0.56  cnf(c_0_56, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.56  cnf(c_0_57, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_58, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))|~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.56  cnf(c_0_59, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0))|~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.56  cnf(c_0_60, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.56  cnf(c_0_61, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.56  cnf(c_0_62, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X4,X3)|~r1_xboole_0(X4,X2)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.56  cnf(c_0_63, plain, (r1_xboole_0(k7_subset_1(X1,X2,X3),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 0.20/0.56  cnf(c_0_64, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_44]), c_0_32])])).
% 0.20/0.56  cnf(c_0_65, negated_conjecture, (~m1_subset_1(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0))|~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_42])])).
% 0.20/0.56  cnf(c_0_66, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(X5))|~r1_xboole_0(k7_subset_1(X5,X4,X3),X2)|~r1_tarski(X1,k7_subset_1(X5,X4,X3))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.56  cnf(c_0_67, negated_conjecture, (r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_32])).
% 0.20/0.56  cnf(c_0_68, negated_conjecture, (~m1_subset_1(k7_subset_1(X1,esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(X1,esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_49]), c_0_42])]), c_0_44])).
% 0.20/0.56  fof(c_0_69, plain, ![X27, X28]:(~l1_pre_topc(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|m1_subset_1(k1_tops_1(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.20/0.56  fof(c_0_70, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|m1_subset_1(k7_subset_1(X21,X22,X23),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).
% 0.20/0.56  cnf(c_0_71, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_72, negated_conjecture, (r1_xboole_0(X1,k2_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0),esk3_0))|~r1_tarski(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_42])])).
% 0.20/0.56  fof(c_0_73, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|r1_tarski(k1_tops_1(X29,X30),X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.20/0.56  cnf(c_0_74, negated_conjecture, (~m1_subset_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(k1_tops_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_26])).
% 0.20/0.56  cnf(c_0_75, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.56  cnf(c_0_76, plain, (m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.56  cnf(c_0_77, negated_conjecture, (r1_xboole_0(X1,esk3_0)|~r1_tarski(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.56  cnf(c_0_78, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.56  cnf(c_0_79, negated_conjecture, (~m1_subset_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(k1_tops_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_61]), c_0_42])])).
% 0.20/0.56  cnf(c_0_80, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_76, c_0_26])).
% 0.20/0.56  cnf(c_0_81, negated_conjecture, (r1_xboole_0(k1_tops_1(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),esk3_0)|~l1_pre_topc(X1)|~m1_subset_1(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.56  cnf(c_0_82, negated_conjecture, (~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_xboole_0(k1_tops_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_42])])).
% 0.20/0.56  cnf(c_0_83, negated_conjecture, (r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_76]), c_0_61]), c_0_42])])).
% 0.20/0.56  cnf(c_0_84, negated_conjecture, (~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(X2,esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_82, c_0_26])).
% 0.20/0.56  cnf(c_0_85, negated_conjecture, (r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_83])).
% 0.20/0.56  cnf(c_0_86, negated_conjecture, (~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_42])])).
% 0.20/0.56  cnf(c_0_87, negated_conjecture, (~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_78]), c_0_61]), c_0_32])])).
% 0.20/0.56  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_42, c_0_87]), ['proof']).
% 0.20/0.56  # SZS output end CNFRefutation
% 0.20/0.56  # Proof object total steps             : 89
% 0.20/0.56  # Proof object clause steps            : 62
% 0.20/0.56  # Proof object formula steps           : 27
% 0.20/0.56  # Proof object conjectures             : 36
% 0.20/0.56  # Proof object clause conjectures      : 33
% 0.20/0.56  # Proof object formula conjectures     : 3
% 0.20/0.56  # Proof object initial clauses used    : 18
% 0.20/0.56  # Proof object initial formulas used   : 13
% 0.20/0.56  # Proof object generating inferences   : 39
% 0.20/0.56  # Proof object simplifying inferences  : 32
% 0.20/0.56  # Training examples: 0 positive, 0 negative
% 0.20/0.56  # Parsed axioms                        : 13
% 0.20/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.56  # Initial clauses                      : 19
% 0.20/0.56  # Removed in clause preprocessing      : 1
% 0.20/0.56  # Initial clauses in saturation        : 18
% 0.20/0.56  # Processed clauses                    : 1164
% 0.20/0.56  # ...of these trivial                  : 3
% 0.20/0.56  # ...subsumed                          : 512
% 0.20/0.56  # ...remaining for further processing  : 649
% 0.20/0.56  # Other redundant clauses eliminated   : 0
% 0.20/0.56  # Clauses deleted for lack of memory   : 0
% 0.20/0.56  # Backward-subsumed                    : 41
% 0.20/0.56  # Backward-rewritten                   : 38
% 0.20/0.56  # Generated clauses                    : 8000
% 0.20/0.56  # ...of the previous two non-trivial   : 7908
% 0.20/0.56  # Contextual simplify-reflections      : 3
% 0.20/0.56  # Paramodulations                      : 7999
% 0.20/0.56  # Factorizations                       : 0
% 0.20/0.56  # Equation resolutions                 : 0
% 0.20/0.56  # Propositional unsat checks           : 0
% 0.20/0.56  #    Propositional check models        : 0
% 0.20/0.56  #    Propositional check unsatisfiable : 0
% 0.20/0.56  #    Propositional clauses             : 0
% 0.20/0.56  #    Propositional clauses after purity: 0
% 0.20/0.56  #    Propositional unsat core size     : 0
% 0.20/0.56  #    Propositional preprocessing time  : 0.000
% 0.20/0.56  #    Propositional encoding time       : 0.000
% 0.20/0.56  #    Propositional solver time         : 0.000
% 0.20/0.56  #    Success case prop preproc time    : 0.000
% 0.20/0.56  #    Success case prop encoding time   : 0.000
% 0.20/0.56  #    Success case prop solver time     : 0.000
% 0.20/0.56  # Current number of processed clauses  : 551
% 0.20/0.56  #    Positive orientable unit clauses  : 41
% 0.20/0.56  #    Positive unorientable unit clauses: 0
% 0.20/0.56  #    Negative unit clauses             : 2
% 0.20/0.56  #    Non-unit-clauses                  : 508
% 0.20/0.56  # Current number of unprocessed clauses: 6764
% 0.20/0.56  # ...number of literals in the above   : 27014
% 0.20/0.56  # Current number of archived formulas  : 0
% 0.20/0.56  # Current number of archived clauses   : 99
% 0.20/0.56  # Clause-clause subsumption calls (NU) : 67359
% 0.20/0.56  # Rec. Clause-clause subsumption calls : 25644
% 0.20/0.56  # Non-unit clause-clause subsumptions  : 556
% 0.20/0.56  # Unit Clause-clause subsumption calls : 5293
% 0.20/0.56  # Rewrite failures with RHS unbound    : 0
% 0.20/0.56  # BW rewrite match attempts            : 152
% 0.20/0.56  # BW rewrite match successes           : 35
% 0.20/0.56  # Condensation attempts                : 0
% 0.20/0.56  # Condensation successes               : 0
% 0.20/0.56  # Termbank termtop insertions          : 177811
% 0.20/0.56  
% 0.20/0.56  # -------------------------------------------------
% 0.20/0.56  # User time                : 0.211 s
% 0.20/0.56  # System time              : 0.007 s
% 0.20/0.56  # Total time               : 0.218 s
% 0.20/0.56  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
