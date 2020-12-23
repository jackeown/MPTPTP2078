%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:11 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 181 expanded)
%              Number of clauses        :   39 (  65 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 874 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(t20_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v8_pre_topc(X1)
                  & v2_compts_1(X2,X1)
                  & v2_compts_1(X3,X1) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(t18_compts_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_compts_1(X2,X1)
                  & r1_tarski(X3,X2)
                  & v4_pre_topc(X3,X1) )
               => v2_compts_1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t35_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & v4_pre_topc(X3,X1) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

fof(t16_compts_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v8_pre_topc(X1)
              & v2_compts_1(X2,X1) )
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

fof(c_0_13,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_14,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | u1_struct_0(k1_pre_topc(X22,X23)) = X23 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v8_pre_topc(X1)
                    & v2_compts_1(X2,X1)
                    & v2_compts_1(X3,X1) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_compts_1])).

cnf(c_0_16,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v8_pre_topc(esk1_0)
    & v2_compts_1(esk2_0,esk1_0)
    & v2_compts_1(esk3_0,esk1_0)
    & ~ v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k9_subset_1(X13,X14,X15) = k3_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_20,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(k1_pre_topc(X3,X4),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ( v1_pre_topc(k1_pre_topc(X20,X21))
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( m1_pre_topc(k1_pre_topc(X20,X21),X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_25,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X32,X33,X34] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ v2_compts_1(X33,X32)
      | ~ r1_tarski(X34,X33)
      | ~ v4_pre_topc(X34,X32)
      | v2_compts_1(X34,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_compts_1])])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(k1_pre_topc(esk1_0,esk3_0),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k9_subset_1(X10,X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_31,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X2,X1)
    | ~ r1_tarski(X3,X2)
    | ~ v4_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23]),c_0_22])])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_36,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_37,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_38,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v2_compts_1(X1,esk1_0)
    | ~ v2_compts_1(X2,esk1_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_23])])).

cnf(c_0_41,negated_conjecture,
    ( v2_compts_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X27,X28,X29] :
      ( ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ v4_pre_topc(X28,X27)
      | ~ v4_pre_topc(X29,X27)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X27),X28,X29),X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_1])])])).

fof(c_0_44,plain,(
    ! [X30,X31] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ v8_pre_topc(X30)
      | ~ v2_compts_1(X31,X30)
      | v4_pre_topc(X31,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( v2_compts_1(X1,esk1_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_22]),c_0_41])]),c_0_42])).

cnf(c_0_52,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_compts_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( v8_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(X1,esk3_0,esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_22]),c_0_50])])).

cnf(c_0_59,negated_conjecture,
    ( v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),X1,X2),esk1_0)
    | ~ v4_pre_topc(X2,esk1_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,X2),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_34]),c_0_23])])).

cnf(c_0_60,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_54]),c_0_55]),c_0_34]),c_0_23])])).

cnf(c_0_61,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_22]),c_0_41]),c_0_55]),c_0_34]),c_0_23])])).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_50]),c_0_60]),c_0_61]),c_0_22])])).

cnf(c_0_64,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:47:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.56/0.78  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.56/0.78  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.56/0.78  #
% 0.56/0.78  # Preprocessing time       : 0.027 s
% 0.56/0.78  # Presaturation interreduction done
% 0.56/0.78  
% 0.56/0.78  # Proof found!
% 0.56/0.78  # SZS status Theorem
% 0.56/0.78  # SZS output start CNFRefutation
% 0.56/0.78  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.56/0.78  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.56/0.78  fof(t20_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v8_pre_topc(X1)&v2_compts_1(X2,X1))&v2_compts_1(X3,X1))=>v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 0.56/0.78  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.56/0.78  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.56/0.78  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.56/0.78  fof(t18_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v2_compts_1(X2,X1)&r1_tarski(X3,X2))&v4_pre_topc(X3,X1))=>v2_compts_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 0.56/0.78  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.56/0.78  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.56/0.78  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.56/0.78  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.56/0.78  fof(t35_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&v4_pre_topc(X3,X1))=>v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 0.56/0.78  fof(t16_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v8_pre_topc(X1)&v2_compts_1(X2,X1))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 0.56/0.78  fof(c_0_13, plain, ![X24, X25, X26]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,X24)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.56/0.78  fof(c_0_14, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|u1_struct_0(k1_pre_topc(X22,X23))=X23)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.56/0.78  fof(c_0_15, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v8_pre_topc(X1)&v2_compts_1(X2,X1))&v2_compts_1(X3,X1))=>v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t20_compts_1])).
% 0.56/0.78  cnf(c_0_16, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.56/0.78  cnf(c_0_17, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.56/0.78  fof(c_0_18, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((v8_pre_topc(esk1_0)&v2_compts_1(esk2_0,esk1_0))&v2_compts_1(esk3_0,esk1_0))&~v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.56/0.78  fof(c_0_19, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X13))|k9_subset_1(X13,X14,X15)=k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.56/0.78  fof(c_0_20, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.56/0.78  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(k1_pre_topc(X3,X4),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.56/0.78  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.78  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.78  fof(c_0_24, plain, ![X20, X21]:((v1_pre_topc(k1_pre_topc(X20,X21))|(~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))))&(m1_pre_topc(k1_pre_topc(X20,X21),X20)|(~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.56/0.78  cnf(c_0_25, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.56/0.78  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.56/0.78  fof(c_0_27, plain, ![X32, X33, X34]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|(~v2_compts_1(X33,X32)|~r1_tarski(X34,X33)|~v4_pre_topc(X34,X32)|v2_compts_1(X34,X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_compts_1])])])).
% 0.56/0.78  cnf(c_0_28, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(k1_pre_topc(esk1_0,esk3_0),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.56/0.78  cnf(c_0_29, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.56/0.78  fof(c_0_30, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k9_subset_1(X10,X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.56/0.78  cnf(c_0_31, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.56/0.78  cnf(c_0_32, plain, (v2_compts_1(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_compts_1(X2,X1)|~r1_tarski(X3,X2)|~v4_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.56/0.78  cnf(c_0_33, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23]), c_0_22])])).
% 0.56/0.78  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.78  fof(c_0_35, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.56/0.78  fof(c_0_36, plain, ![X6, X7]:r1_tarski(k4_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.56/0.78  fof(c_0_37, plain, ![X8, X9]:k4_xboole_0(X8,k4_xboole_0(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.56/0.78  cnf(c_0_38, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.56/0.78  cnf(c_0_39, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_31, c_0_31])).
% 0.56/0.78  cnf(c_0_40, negated_conjecture, (v2_compts_1(X1,esk1_0)|~v2_compts_1(X2,esk1_0)|~v4_pre_topc(X1,esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_23])])).
% 0.56/0.78  cnf(c_0_41, negated_conjecture, (v2_compts_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.78  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.56/0.78  fof(c_0_43, plain, ![X27, X28, X29]:(~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(~v4_pre_topc(X28,X27)|~v4_pre_topc(X29,X27)|v4_pre_topc(k9_subset_1(u1_struct_0(X27),X28,X29),X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_1])])])).
% 0.56/0.78  fof(c_0_44, plain, ![X30, X31]:(~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~v8_pre_topc(X30)|~v2_compts_1(X31,X30)|v4_pre_topc(X31,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).
% 0.56/0.78  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.56/0.78  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.56/0.78  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.56/0.78  cnf(c_0_48, negated_conjecture, (~v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.78  cnf(c_0_49, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X4,X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.56/0.78  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.78  cnf(c_0_51, negated_conjecture, (v2_compts_1(X1,esk1_0)|~v4_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_22]), c_0_41])]), c_0_42])).
% 0.56/0.78  cnf(c_0_52, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v4_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.56/0.78  cnf(c_0_53, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v8_pre_topc(X1)|~v2_compts_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.56/0.78  cnf(c_0_54, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.78  cnf(c_0_55, negated_conjecture, (v8_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.78  cnf(c_0_56, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.56/0.78  cnf(c_0_57, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_47, c_0_26])).
% 0.56/0.78  cnf(c_0_58, negated_conjecture, (~v2_compts_1(k9_subset_1(X1,esk3_0,esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_22]), c_0_50])])).
% 0.56/0.78  cnf(c_0_59, negated_conjecture, (v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),X1,X2),esk1_0)|~v4_pre_topc(X2,esk1_0)|~v4_pre_topc(X1,esk1_0)|~m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,X2),k1_zfmisc_1(esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_34]), c_0_23])])).
% 0.56/0.78  cnf(c_0_60, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_54]), c_0_55]), c_0_34]), c_0_23])])).
% 0.56/0.78  cnf(c_0_61, negated_conjecture, (v4_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_22]), c_0_41]), c_0_55]), c_0_34]), c_0_23])])).
% 0.56/0.78  cnf(c_0_62, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.56/0.78  cnf(c_0_63, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_50]), c_0_60]), c_0_61]), c_0_22])])).
% 0.56/0.78  cnf(c_0_64, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_31])).
% 0.56/0.78  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_50])]), ['proof']).
% 0.56/0.78  # SZS output end CNFRefutation
% 0.56/0.78  # Proof object total steps             : 66
% 0.56/0.78  # Proof object clause steps            : 39
% 0.56/0.78  # Proof object formula steps           : 27
% 0.56/0.78  # Proof object conjectures             : 21
% 0.56/0.78  # Proof object clause conjectures      : 18
% 0.56/0.78  # Proof object formula conjectures     : 3
% 0.56/0.78  # Proof object initial clauses used    : 21
% 0.56/0.78  # Proof object initial formulas used   : 13
% 0.56/0.78  # Proof object generating inferences   : 16
% 0.56/0.78  # Proof object simplifying inferences  : 36
% 0.56/0.78  # Training examples: 0 positive, 0 negative
% 0.56/0.78  # Parsed axioms                        : 14
% 0.56/0.78  # Removed by relevancy pruning/SinE    : 0
% 0.56/0.78  # Initial clauses                      : 23
% 0.56/0.78  # Removed in clause preprocessing      : 1
% 0.56/0.78  # Initial clauses in saturation        : 22
% 0.56/0.78  # Processed clauses                    : 5134
% 0.56/0.78  # ...of these trivial                  : 34
% 0.56/0.78  # ...subsumed                          : 4275
% 0.56/0.78  # ...remaining for further processing  : 825
% 0.56/0.78  # Other redundant clauses eliminated   : 0
% 0.56/0.78  # Clauses deleted for lack of memory   : 0
% 0.56/0.78  # Backward-subsumed                    : 77
% 0.56/0.78  # Backward-rewritten                   : 15
% 0.56/0.78  # Generated clauses                    : 24671
% 0.56/0.78  # ...of the previous two non-trivial   : 20847
% 0.56/0.78  # Contextual simplify-reflections      : 16
% 0.56/0.78  # Paramodulations                      : 24671
% 0.56/0.78  # Factorizations                       : 0
% 0.56/0.78  # Equation resolutions                 : 0
% 0.56/0.78  # Propositional unsat checks           : 0
% 0.56/0.78  #    Propositional check models        : 0
% 0.56/0.78  #    Propositional check unsatisfiable : 0
% 0.56/0.78  #    Propositional clauses             : 0
% 0.56/0.78  #    Propositional clauses after purity: 0
% 0.56/0.78  #    Propositional unsat core size     : 0
% 0.56/0.78  #    Propositional preprocessing time  : 0.000
% 0.56/0.78  #    Propositional encoding time       : 0.000
% 0.56/0.78  #    Propositional solver time         : 0.000
% 0.56/0.78  #    Success case prop preproc time    : 0.000
% 0.56/0.78  #    Success case prop encoding time   : 0.000
% 0.56/0.78  #    Success case prop solver time     : 0.000
% 0.56/0.78  # Current number of processed clauses  : 711
% 0.56/0.78  #    Positive orientable unit clauses  : 38
% 0.56/0.78  #    Positive unorientable unit clauses: 1
% 0.56/0.78  #    Negative unit clauses             : 6
% 0.56/0.78  #    Non-unit-clauses                  : 666
% 0.56/0.78  # Current number of unprocessed clauses: 15501
% 0.56/0.78  # ...number of literals in the above   : 75418
% 0.56/0.78  # Current number of archived formulas  : 0
% 0.56/0.78  # Current number of archived clauses   : 115
% 0.56/0.78  # Clause-clause subsumption calls (NU) : 81296
% 0.56/0.78  # Rec. Clause-clause subsumption calls : 33523
% 0.56/0.78  # Non-unit clause-clause subsumptions  : 3364
% 0.56/0.78  # Unit Clause-clause subsumption calls : 187
% 0.56/0.78  # Rewrite failures with RHS unbound    : 0
% 0.56/0.78  # BW rewrite match attempts            : 27
% 0.56/0.78  # BW rewrite match successes           : 17
% 0.56/0.78  # Condensation attempts                : 0
% 0.56/0.78  # Condensation successes               : 0
% 0.56/0.78  # Termbank termtop insertions          : 466072
% 0.56/0.78  
% 0.56/0.78  # -------------------------------------------------
% 0.56/0.78  # User time                : 0.418 s
% 0.56/0.78  # System time              : 0.023 s
% 0.56/0.78  # Total time               : 0.441 s
% 0.56/0.78  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
