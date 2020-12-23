%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:02 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 904 expanded)
%              Number of clauses        :   58 ( 413 expanded)
%              Number of leaves         :   11 ( 228 expanded)
%              Depth                    :   20
%              Number of atoms          :  219 (2308 expanded)
%              Number of equality atoms :   17 ( 324 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(t19_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( r1_tarski(X2,X3)
                  & v2_tops_2(X3,X1) )
               => v2_tops_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t52_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(k7_setfam_1(X1,X2),X3)
          <=> r1_tarski(X2,k7_setfam_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t18_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( r1_tarski(X2,X3)
                  & v1_tops_2(X3,X1) )
               => v1_tops_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(t16_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

fof(c_0_11,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | m1_subset_1(k9_subset_1(X10,X11,X12),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_12,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k9_subset_1(X13,X14,X15) = k3_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_13,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_xboole_0(X4,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))
      | m1_subset_1(k7_setfam_1(X16,X17),k1_zfmisc_1(k1_zfmisc_1(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( ( r1_tarski(X2,X3)
                    & v2_tops_2(X3,X1) )
                 => v2_tops_2(X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_tops_2])).

fof(c_0_22,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_23,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r1_tarski(k7_setfam_1(X20,X21),X22)
        | r1_tarski(X21,k7_setfam_1(X20,X22))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X20)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))) )
      & ( ~ r1_tarski(X21,k7_setfam_1(X20,X22))
        | r1_tarski(k7_setfam_1(X20,X21),X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X20)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_setfam_1])])])])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18)))
      | k7_setfam_1(X18,k7_setfam_1(X18,X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & r1_tarski(esk2_0,esk3_0)
    & v2_tops_2(esk3_0,esk1_0)
    & ~ v2_tops_2(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(X2,k7_setfam_1(X1,X3))
    | ~ r1_tarski(k7_setfam_1(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r1_tarski(X4,k7_setfam_1(X2,X3))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_34,plain,
    ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X2,k7_setfam_1(u1_struct_0(esk1_0),esk2_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_36,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_37,plain,
    ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X2))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_40])).

fof(c_0_45,plain,(
    ! [X25,X26,X27] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
      | ~ r1_tarski(X26,X27)
      | ~ v1_tops_2(X27,X25)
      | v1_tops_2(X26,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tops_2])])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X2,k7_setfam_1(u1_struct_0(esk1_0),esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),X1),k7_setfam_1(u1_struct_0(esk1_0),X1))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,plain,
    ( v1_tops_2(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X3)
    | ~ v1_tops_2(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_49])])).

cnf(c_0_54,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X2),X3),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X2),X3)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_44])).

cnf(c_0_58,plain,
    ( r1_tarski(k7_setfam_1(X2,X1),X3)
    | ~ r1_tarski(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0))
    | ~ r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( v1_tops_2(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X1),esk1_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),X2),esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X1),k7_setfam_1(u1_struct_0(esk1_0),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

fof(c_0_61,plain,(
    ! [X23,X24] :
      ( ( ~ v2_tops_2(X24,X23)
        | v1_tops_2(k7_setfam_1(u1_struct_0(X23),X24),X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ l1_pre_topc(X23) )
      & ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X23),X24),X23)
        | v2_tops_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tops_2])])])])).

cnf(c_0_62,plain,
    ( X1 = k7_setfam_1(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r1_tarski(X1,k7_setfam_1(X2,X3))
    | ~ r1_tarski(X3,k7_setfam_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_30]),c_0_49]),c_0_32])])).

cnf(c_0_64,negated_conjecture,
    ( v1_tops_2(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X1),esk1_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_28]),c_0_41])])).

cnf(c_0_65,plain,
    ( v2_tops_2(X2,X1)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k7_setfam_1(u1_struct_0(esk1_0),X1) = esk2_0
    | ~ r1_tarski(esk2_0,k7_setfam_1(u1_struct_0(esk1_0),X1))
    | ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_32]),c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk2_0,k7_setfam_1(u1_struct_0(esk1_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_63]),c_0_53]),c_0_32])])).

cnf(c_0_68,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),esk1_0)
    | ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(esk1_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_44])).

cnf(c_0_69,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( v2_tops_2(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_71,plain,
    ( r1_tarski(k7_setfam_1(X1,X2),X3)
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X2,k7_setfam_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_26])).

cnf(c_0_72,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v1_tops_2(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_30]),c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( k7_setfam_1(u1_struct_0(esk1_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_63])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_tops_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(esk1_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_56]),c_0_41])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(esk2_0,k7_setfam_1(u1_struct_0(esk1_0),X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_53])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_56]),c_0_53])]),c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(esk2_0,k7_setfam_1(u1_struct_0(esk1_0),k7_setfam_1(u1_struct_0(esk1_0),esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_30]),c_0_49]),c_0_41])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_26]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n007.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 19:14:36 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.12/0.31  # No SInE strategy applied
% 0.12/0.31  # Trying AutoSched0 for 299 seconds
% 0.52/0.75  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.52/0.75  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.52/0.75  #
% 0.52/0.75  # Preprocessing time       : 0.028 s
% 0.52/0.75  # Presaturation interreduction done
% 0.52/0.75  
% 0.52/0.75  # Proof found!
% 0.52/0.75  # SZS status Theorem
% 0.52/0.75  # SZS output start CNFRefutation
% 0.52/0.75  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.52/0.75  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.52/0.75  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.52/0.75  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.52/0.75  fof(t19_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((r1_tarski(X2,X3)&v2_tops_2(X3,X1))=>v2_tops_2(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 0.52/0.75  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.52/0.75  fof(t52_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(k7_setfam_1(X1,X2),X3)<=>r1_tarski(X2,k7_setfam_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_setfam_1)).
% 0.52/0.75  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.52/0.75  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.52/0.75  fof(t18_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((r1_tarski(X2,X3)&v1_tops_2(X3,X1))=>v1_tops_2(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 0.52/0.75  fof(t16_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tops_2)).
% 0.52/0.75  fof(c_0_11, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|m1_subset_1(k9_subset_1(X10,X11,X12),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.52/0.75  fof(c_0_12, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X13))|k9_subset_1(X13,X14,X15)=k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.52/0.75  cnf(c_0_13, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.52/0.75  cnf(c_0_14, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.52/0.75  fof(c_0_15, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.52/0.75  cnf(c_0_16, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.52/0.75  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.52/0.75  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.52/0.75  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_xboole_0(X4,X3))), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.52/0.75  fof(c_0_20, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))|m1_subset_1(k7_setfam_1(X16,X17),k1_zfmisc_1(k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.52/0.75  fof(c_0_21, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((r1_tarski(X2,X3)&v2_tops_2(X3,X1))=>v2_tops_2(X2,X1)))))), inference(assume_negation,[status(cth)],[t19_tops_2])).
% 0.52/0.75  fof(c_0_22, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.52/0.75  fof(c_0_23, plain, ![X20, X21, X22]:((~r1_tarski(k7_setfam_1(X20,X21),X22)|r1_tarski(X21,k7_setfam_1(X20,X22))|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X20)))|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))))&(~r1_tarski(X21,k7_setfam_1(X20,X22))|r1_tarski(k7_setfam_1(X20,X21),X22)|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X20)))|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_setfam_1])])])])).
% 0.52/0.75  fof(c_0_24, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18)))|k7_setfam_1(X18,k7_setfam_1(X18,X19))=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.52/0.75  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 0.52/0.75  cnf(c_0_26, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.52/0.75  fof(c_0_27, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&((r1_tarski(esk2_0,esk3_0)&v2_tops_2(esk3_0,esk1_0))&~v2_tops_2(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.52/0.75  cnf(c_0_28, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.52/0.75  cnf(c_0_29, plain, (r1_tarski(X2,k7_setfam_1(X1,X3))|~r1_tarski(k7_setfam_1(X1,X2),X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.52/0.75  cnf(c_0_30, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.52/0.75  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r1_tarski(X4,k7_setfam_1(X2,X3))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.52/0.75  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.75  cnf(c_0_33, plain, (r1_tarski(X1,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_17])).
% 0.52/0.75  cnf(c_0_34, plain, (r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_18])).
% 0.52/0.75  cnf(c_0_35, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X2,k7_setfam_1(u1_struct_0(esk1_0),esk2_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.52/0.75  fof(c_0_36, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.52/0.75  cnf(c_0_37, plain, (r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X2))|~m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.52/0.75  cnf(c_0_38, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X1,k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),X2))), inference(spm,[status(thm)],[c_0_35, c_0_28])).
% 0.52/0.75  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.52/0.75  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.52/0.75  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.75  cnf(c_0_42, plain, (r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X2))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_18])).
% 0.52/0.75  cnf(c_0_43, negated_conjecture, (m1_subset_1(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.52/0.75  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_40])).
% 0.52/0.75  fof(c_0_45, plain, ![X25, X26, X27]:(~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))|(~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))|(~r1_tarski(X26,X27)|~v1_tops_2(X27,X25)|v1_tops_2(X26,X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tops_2])])])).
% 0.52/0.75  cnf(c_0_46, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X2,k7_setfam_1(u1_struct_0(esk1_0),esk3_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_41])).
% 0.52/0.75  cnf(c_0_47, negated_conjecture, (r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),X1),k7_setfam_1(u1_struct_0(esk1_0),X1))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 0.52/0.75  cnf(c_0_48, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X1,k7_setfam_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.52/0.75  cnf(c_0_49, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.75  cnf(c_0_50, plain, (v1_tops_2(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~r1_tarski(X2,X3)|~v1_tops_2(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.52/0.75  cnf(c_0_51, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X1,k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X2))), inference(spm,[status(thm)],[c_0_46, c_0_28])).
% 0.52/0.75  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),X1),esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_30])).
% 0.52/0.75  cnf(c_0_53, negated_conjecture, (m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_47]), c_0_49])])).
% 0.52/0.75  cnf(c_0_54, plain, (v1_tops_2(X1,X2)|~v1_tops_2(k7_setfam_1(u1_struct_0(X2),X3),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,k7_setfam_1(u1_struct_0(X2),X3))), inference(spm,[status(thm)],[c_0_50, c_0_26])).
% 0.52/0.75  cnf(c_0_55, negated_conjecture, (m1_subset_1(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_51, c_0_39])).
% 0.52/0.75  cnf(c_0_56, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.75  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_44])).
% 0.52/0.75  cnf(c_0_58, plain, (r1_tarski(k7_setfam_1(X2,X1),X3)|~r1_tarski(X1,k7_setfam_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.52/0.75  cnf(c_0_59, negated_conjecture, (r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0))|~r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.52/0.75  cnf(c_0_60, negated_conjecture, (v1_tops_2(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X1),esk1_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),X2),esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X1),k7_setfam_1(u1_struct_0(esk1_0),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.52/0.75  fof(c_0_61, plain, ![X23, X24]:((~v2_tops_2(X24,X23)|v1_tops_2(k7_setfam_1(u1_struct_0(X23),X24),X23)|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~l1_pre_topc(X23))&(~v1_tops_2(k7_setfam_1(u1_struct_0(X23),X24),X23)|v2_tops_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~l1_pre_topc(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tops_2])])])])).
% 0.52/0.75  cnf(c_0_62, plain, (X1=k7_setfam_1(X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r1_tarski(X1,k7_setfam_1(X2,X3))|~r1_tarski(X3,k7_setfam_1(X2,X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.52/0.75  cnf(c_0_63, negated_conjecture, (r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_30]), c_0_49]), c_0_32])])).
% 0.52/0.75  cnf(c_0_64, negated_conjecture, (v1_tops_2(k3_xboole_0(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),X1),esk1_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_28]), c_0_41])])).
% 0.52/0.75  cnf(c_0_65, plain, (v2_tops_2(X2,X1)|~v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.52/0.75  cnf(c_0_66, negated_conjecture, (k7_setfam_1(u1_struct_0(esk1_0),X1)=esk2_0|~r1_tarski(esk2_0,k7_setfam_1(u1_struct_0(esk1_0),X1))|~r1_tarski(X1,k7_setfam_1(u1_struct_0(esk1_0),esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_32]), c_0_48])).
% 0.52/0.75  cnf(c_0_67, negated_conjecture, (r1_tarski(esk2_0,k7_setfam_1(u1_struct_0(esk1_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_63]), c_0_53]), c_0_32])])).
% 0.52/0.75  cnf(c_0_68, negated_conjecture, (v1_tops_2(X1,esk1_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),esk1_0)|~r1_tarski(X1,k7_setfam_1(u1_struct_0(esk1_0),esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_44])).
% 0.52/0.75  cnf(c_0_69, plain, (v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)|~v2_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.52/0.75  cnf(c_0_70, negated_conjecture, (v2_tops_2(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.75  cnf(c_0_71, plain, (r1_tarski(k7_setfam_1(X1,X2),X3)|~m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(X2,k7_setfam_1(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_30]), c_0_26])).
% 0.52/0.75  cnf(c_0_72, plain, (v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)|~v1_tops_2(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_30]), c_0_26])).
% 0.52/0.75  cnf(c_0_73, negated_conjecture, (k7_setfam_1(u1_struct_0(esk1_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_63])])).
% 0.52/0.75  cnf(c_0_74, negated_conjecture, (~v2_tops_2(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.75  cnf(c_0_75, negated_conjecture, (v1_tops_2(X1,esk1_0)|~r1_tarski(X1,k7_setfam_1(u1_struct_0(esk1_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_56]), c_0_41])])).
% 0.52/0.75  cnf(c_0_76, negated_conjecture, (r1_tarski(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(esk2_0,k7_setfam_1(u1_struct_0(esk1_0),X1))), inference(spm,[status(thm)],[c_0_71, c_0_53])).
% 0.52/0.75  cnf(c_0_77, negated_conjecture, (~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_56]), c_0_53])]), c_0_74])).
% 0.52/0.75  cnf(c_0_78, negated_conjecture, (~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(esk2_0,k7_setfam_1(u1_struct_0(esk1_0),k7_setfam_1(u1_struct_0(esk1_0),esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.52/0.75  cnf(c_0_79, negated_conjecture, (~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_30]), c_0_49]), c_0_41])])).
% 0.52/0.75  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_26]), c_0_41])]), ['proof']).
% 0.52/0.75  # SZS output end CNFRefutation
% 0.52/0.75  # Proof object total steps             : 81
% 0.52/0.75  # Proof object clause steps            : 58
% 0.52/0.75  # Proof object formula steps           : 23
% 0.52/0.75  # Proof object conjectures             : 33
% 0.52/0.75  # Proof object clause conjectures      : 30
% 0.52/0.75  # Proof object formula conjectures     : 3
% 0.52/0.75  # Proof object initial clauses used    : 18
% 0.52/0.75  # Proof object initial formulas used   : 11
% 0.52/0.75  # Proof object generating inferences   : 40
% 0.52/0.75  # Proof object simplifying inferences  : 33
% 0.52/0.75  # Training examples: 0 positive, 0 negative
% 0.52/0.75  # Parsed axioms                        : 11
% 0.52/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.52/0.75  # Initial clauses                      : 18
% 0.52/0.75  # Removed in clause preprocessing      : 0
% 0.52/0.75  # Initial clauses in saturation        : 18
% 0.52/0.75  # Processed clauses                    : 4829
% 0.52/0.75  # ...of these trivial                  : 68
% 0.52/0.75  # ...subsumed                          : 3624
% 0.52/0.75  # ...remaining for further processing  : 1137
% 0.52/0.75  # Other redundant clauses eliminated   : 0
% 0.52/0.75  # Clauses deleted for lack of memory   : 0
% 0.52/0.75  # Backward-subsumed                    : 163
% 0.52/0.75  # Backward-rewritten                   : 26
% 0.52/0.75  # Generated clauses                    : 18840
% 0.52/0.75  # ...of the previous two non-trivial   : 17667
% 0.52/0.75  # Contextual simplify-reflections      : 168
% 0.52/0.75  # Paramodulations                      : 18840
% 0.52/0.75  # Factorizations                       : 0
% 0.52/0.75  # Equation resolutions                 : 0
% 0.52/0.75  # Propositional unsat checks           : 0
% 0.52/0.75  #    Propositional check models        : 0
% 0.52/0.75  #    Propositional check unsatisfiable : 0
% 0.52/0.75  #    Propositional clauses             : 0
% 0.52/0.75  #    Propositional clauses after purity: 0
% 0.52/0.75  #    Propositional unsat core size     : 0
% 0.52/0.75  #    Propositional preprocessing time  : 0.000
% 0.52/0.75  #    Propositional encoding time       : 0.000
% 0.52/0.75  #    Propositional solver time         : 0.000
% 0.52/0.75  #    Success case prop preproc time    : 0.000
% 0.52/0.75  #    Success case prop encoding time   : 0.000
% 0.52/0.75  #    Success case prop solver time     : 0.000
% 0.52/0.75  # Current number of processed clauses  : 930
% 0.52/0.75  #    Positive orientable unit clauses  : 57
% 0.52/0.75  #    Positive unorientable unit clauses: 1
% 0.52/0.75  #    Negative unit clauses             : 6
% 0.52/0.75  #    Non-unit-clauses                  : 866
% 0.52/0.75  # Current number of unprocessed clauses: 12772
% 0.52/0.75  # ...number of literals in the above   : 51862
% 0.52/0.75  # Current number of archived formulas  : 0
% 0.52/0.75  # Current number of archived clauses   : 207
% 0.52/0.75  # Clause-clause subsumption calls (NU) : 306148
% 0.52/0.75  # Rec. Clause-clause subsumption calls : 106316
% 0.52/0.75  # Non-unit clause-clause subsumptions  : 3288
% 0.52/0.75  # Unit Clause-clause subsumption calls : 1351
% 0.52/0.75  # Rewrite failures with RHS unbound    : 0
% 0.52/0.75  # BW rewrite match attempts            : 268
% 0.52/0.75  # BW rewrite match successes           : 7
% 0.52/0.75  # Condensation attempts                : 0
% 0.52/0.75  # Condensation successes               : 0
% 0.52/0.75  # Termbank termtop insertions          : 408896
% 0.59/0.75  
% 0.59/0.75  # -------------------------------------------------
% 0.59/0.75  # User time                : 0.423 s
% 0.59/0.75  # System time              : 0.015 s
% 0.59/0.75  # Total time               : 0.438 s
% 0.59/0.75  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
