%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:09 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 178 expanded)
%              Number of clauses        :   40 (  68 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 ( 772 expanded)
%              Number of equality atoms :   16 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t16_compts_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v8_pre_topc(X1)
              & v2_compts_1(X2,X1) )
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k3_xboole_0(X9,X10) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_12,plain,(
    ! [X19,X20] : k1_setfam_1(k2_tarski(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(k3_xboole_0(X4,X6),X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_tarski(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_17,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_22,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_23,negated_conjecture,(
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

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v8_pre_topc(esk1_0)
    & v2_compts_1(esk2_0,esk1_0)
    & v2_compts_1(esk3_0,esk1_0)
    & ~ v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_27,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | k9_subset_1(X16,X17,X18) = k3_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_31,plain,(
    ! [X28,X29,X30] :
      ( ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ v2_compts_1(X29,X28)
      | ~ r1_tarski(X30,X29)
      | ~ v4_pre_topc(X30,X28)
      | v2_compts_1(X30,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_compts_1])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_35,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X2,X1)
    | ~ r1_tarski(X3,X2)
    | ~ v4_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_39,plain,(
    ! [X23,X24,X25] :
      ( ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ v4_pre_topc(X24,X23)
      | ~ v4_pre_topc(X25,X23)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X23),X24,X25),X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_1])])])).

fof(c_0_40,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v2_compts_1(X1,esk1_0)
    | ~ v2_compts_1(X2,esk1_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_44,negated_conjecture,
    ( v2_compts_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,plain,(
    ! [X26,X27] :
      ( ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ v8_pre_topc(X26)
      | ~ v2_compts_1(X27,X26)
      | v4_pre_topc(X27,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(X1,esk2_0,esk3_0),esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_29])])).

cnf(c_0_49,negated_conjecture,
    ( v2_compts_1(X1,esk1_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_29]),c_0_44])])).

cnf(c_0_50,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X3)
    | ~ v4_pre_topc(X2,X3)
    | ~ v4_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_51,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_compts_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v8_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(esk2_0,esk3_0)),esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( v2_compts_1(k1_setfam_1(k2_tarski(X1,X2)),esk1_0)
    | ~ v4_pre_topc(X2,esk1_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_37]),c_0_38])])).

cnf(c_0_58,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_29]),c_0_44]),c_0_52]),c_0_37]),c_0_38])])).

cnf(c_0_59,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_53]),c_0_54]),c_0_52]),c_0_37]),c_0_38])])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59]),c_0_29]),c_0_53]),c_0_60])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_29,c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.72/0.89  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.72/0.89  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.72/0.89  #
% 0.72/0.89  # Preprocessing time       : 0.027 s
% 0.72/0.89  # Presaturation interreduction done
% 0.72/0.89  
% 0.72/0.89  # Proof found!
% 0.72/0.89  # SZS status Theorem
% 0.72/0.89  # SZS output start CNFRefutation
% 0.72/0.89  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.72/0.89  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.72/0.89  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.72/0.89  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.72/0.89  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.72/0.89  fof(t20_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v8_pre_topc(X1)&v2_compts_1(X2,X1))&v2_compts_1(X3,X1))=>v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 0.72/0.89  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.72/0.89  fof(t18_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v2_compts_1(X2,X1)&r1_tarski(X3,X2))&v4_pre_topc(X3,X1))=>v2_compts_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 0.72/0.89  fof(t35_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&v4_pre_topc(X3,X1))=>v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 0.72/0.89  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.72/0.89  fof(t16_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v8_pre_topc(X1)&v2_compts_1(X2,X1))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 0.72/0.89  fof(c_0_11, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k3_xboole_0(X9,X10)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.72/0.89  fof(c_0_12, plain, ![X19, X20]:k1_setfam_1(k2_tarski(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.72/0.89  fof(c_0_13, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|r1_tarski(k3_xboole_0(X4,X6),X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.72/0.89  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.72/0.89  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.72/0.89  fof(c_0_16, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_tarski(X12,X11), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.72/0.89  cnf(c_0_17, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.72/0.89  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.72/0.89  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.72/0.89  cnf(c_0_20, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X3)),X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_15])).
% 0.72/0.89  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.72/0.89  fof(c_0_22, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.72/0.89  fof(c_0_23, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v8_pre_topc(X1)&v2_compts_1(X2,X1))&v2_compts_1(X3,X1))=>v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t20_compts_1])).
% 0.72/0.89  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.72/0.89  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.72/0.89  fof(c_0_26, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((v8_pre_topc(esk1_0)&v2_compts_1(esk2_0,esk1_0))&v2_compts_1(esk3_0,esk1_0))&~v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.72/0.89  fof(c_0_27, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X16))|k9_subset_1(X16,X17,X18)=k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.72/0.89  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.72/0.89  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.89  cnf(c_0_30, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.72/0.89  fof(c_0_31, plain, ![X28, X29, X30]:(~v2_pre_topc(X28)|~l1_pre_topc(X28)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|(~v2_compts_1(X29,X28)|~r1_tarski(X30,X29)|~v4_pre_topc(X30,X28)|v2_compts_1(X30,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_compts_1])])])).
% 0.72/0.89  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.72/0.89  cnf(c_0_33, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.72/0.89  cnf(c_0_34, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_30, c_0_15])).
% 0.72/0.89  cnf(c_0_35, plain, (v2_compts_1(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_compts_1(X2,X1)|~r1_tarski(X3,X2)|~v4_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.72/0.89  cnf(c_0_36, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.72/0.89  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.89  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.89  fof(c_0_39, plain, ![X23, X24, X25]:(~v2_pre_topc(X23)|~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~v4_pre_topc(X24,X23)|~v4_pre_topc(X25,X23)|v4_pre_topc(k9_subset_1(u1_struct_0(X23),X24,X25),X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_1])])])).
% 0.72/0.89  fof(c_0_40, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.72/0.89  cnf(c_0_41, negated_conjecture, (~v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.89  cnf(c_0_42, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_34, c_0_34])).
% 0.72/0.89  cnf(c_0_43, negated_conjecture, (v2_compts_1(X1,esk1_0)|~v2_compts_1(X2,esk1_0)|~v4_pre_topc(X1,esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk3_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 0.72/0.89  cnf(c_0_44, negated_conjecture, (v2_compts_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.89  cnf(c_0_45, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v4_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.72/0.89  fof(c_0_46, plain, ![X26, X27]:(~v2_pre_topc(X26)|~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v8_pre_topc(X26)|~v2_compts_1(X27,X26)|v4_pre_topc(X27,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).
% 0.72/0.89  cnf(c_0_47, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.72/0.89  cnf(c_0_48, negated_conjecture, (~v2_compts_1(k9_subset_1(X1,esk2_0,esk3_0),esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_29])])).
% 0.72/0.89  cnf(c_0_49, negated_conjecture, (v2_compts_1(X1,esk1_0)|~v4_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_29]), c_0_44])])).
% 0.72/0.89  cnf(c_0_50, plain, (v4_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X3)|~v4_pre_topc(X2,X3)|~v4_pre_topc(X1,X3)|~l1_pre_topc(X3)|~v2_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_45, c_0_34])).
% 0.72/0.89  cnf(c_0_51, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v8_pre_topc(X1)|~v2_compts_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.72/0.89  cnf(c_0_52, negated_conjecture, (v8_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.89  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.89  cnf(c_0_54, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.72/0.89  cnf(c_0_55, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_47, c_0_15])).
% 0.72/0.89  cnf(c_0_56, negated_conjecture, (~v2_compts_1(k1_setfam_1(k2_tarski(esk2_0,esk3_0)),esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_34])).
% 0.72/0.89  cnf(c_0_57, negated_conjecture, (v2_compts_1(k1_setfam_1(k2_tarski(X1,X2)),esk1_0)|~v4_pre_topc(X2,esk1_0)|~v4_pre_topc(X1,esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_37]), c_0_38])])).
% 0.72/0.89  cnf(c_0_58, negated_conjecture, (v4_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_29]), c_0_44]), c_0_52]), c_0_37]), c_0_38])])).
% 0.72/0.89  cnf(c_0_59, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_53]), c_0_54]), c_0_52]), c_0_37]), c_0_38])])).
% 0.72/0.89  cnf(c_0_60, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_55, c_0_19])).
% 0.72/0.89  cnf(c_0_61, negated_conjecture, (~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59]), c_0_29]), c_0_53]), c_0_60])])).
% 0.72/0.89  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_29, c_0_61]), ['proof']).
% 0.72/0.89  # SZS output end CNFRefutation
% 0.72/0.89  # Proof object total steps             : 63
% 0.72/0.89  # Proof object clause steps            : 40
% 0.72/0.89  # Proof object formula steps           : 23
% 0.72/0.89  # Proof object conjectures             : 22
% 0.72/0.89  # Proof object clause conjectures      : 19
% 0.72/0.89  # Proof object formula conjectures     : 3
% 0.72/0.89  # Proof object initial clauses used    : 19
% 0.72/0.89  # Proof object initial formulas used   : 11
% 0.72/0.89  # Proof object generating inferences   : 16
% 0.72/0.89  # Proof object simplifying inferences  : 31
% 0.72/0.89  # Training examples: 0 positive, 0 negative
% 0.72/0.89  # Parsed axioms                        : 12
% 0.72/0.89  # Removed by relevancy pruning/SinE    : 0
% 0.72/0.89  # Initial clauses                      : 20
% 0.72/0.89  # Removed in clause preprocessing      : 1
% 0.72/0.89  # Initial clauses in saturation        : 19
% 0.72/0.89  # Processed clauses                    : 7015
% 0.72/0.89  # ...of these trivial                  : 148
% 0.72/0.89  # ...subsumed                          : 5655
% 0.72/0.89  # ...remaining for further processing  : 1212
% 0.72/0.89  # Other redundant clauses eliminated   : 0
% 0.72/0.89  # Clauses deleted for lack of memory   : 0
% 0.72/0.89  # Backward-subsumed                    : 37
% 0.72/0.89  # Backward-rewritten                   : 35
% 0.72/0.89  # Generated clauses                    : 50319
% 0.72/0.89  # ...of the previous two non-trivial   : 47908
% 0.72/0.89  # Contextual simplify-reflections      : 1
% 0.72/0.89  # Paramodulations                      : 50317
% 0.72/0.89  # Factorizations                       : 0
% 0.72/0.89  # Equation resolutions                 : 0
% 0.72/0.89  # Propositional unsat checks           : 0
% 0.72/0.89  #    Propositional check models        : 0
% 0.72/0.89  #    Propositional check unsatisfiable : 0
% 0.72/0.89  #    Propositional clauses             : 0
% 0.72/0.89  #    Propositional clauses after purity: 0
% 0.72/0.89  #    Propositional unsat core size     : 0
% 0.72/0.89  #    Propositional preprocessing time  : 0.000
% 0.72/0.89  #    Propositional encoding time       : 0.000
% 0.72/0.89  #    Propositional solver time         : 0.000
% 0.72/0.89  #    Success case prop preproc time    : 0.000
% 0.72/0.89  #    Success case prop encoding time   : 0.000
% 0.72/0.89  #    Success case prop solver time     : 0.000
% 0.72/0.89  # Current number of processed clauses  : 1119
% 0.72/0.89  #    Positive orientable unit clauses  : 104
% 0.72/0.89  #    Positive unorientable unit clauses: 1
% 0.72/0.89  #    Negative unit clauses             : 72
% 0.72/0.89  #    Non-unit-clauses                  : 942
% 0.72/0.89  # Current number of unprocessed clauses: 40711
% 0.72/0.89  # ...number of literals in the above   : 129236
% 0.72/0.89  # Current number of archived formulas  : 0
% 0.72/0.89  # Current number of archived clauses   : 94
% 0.72/0.89  # Clause-clause subsumption calls (NU) : 218024
% 0.72/0.89  # Rec. Clause-clause subsumption calls : 118083
% 0.72/0.89  # Non-unit clause-clause subsumptions  : 4427
% 0.72/0.89  # Unit Clause-clause subsumption calls : 32433
% 0.72/0.89  # Rewrite failures with RHS unbound    : 0
% 0.72/0.89  # BW rewrite match attempts            : 966
% 0.72/0.89  # BW rewrite match successes           : 21
% 0.72/0.89  # Condensation attempts                : 0
% 0.72/0.89  # Condensation successes               : 0
% 0.72/0.89  # Termbank termtop insertions          : 766050
% 0.72/0.89  
% 0.72/0.89  # -------------------------------------------------
% 0.72/0.89  # User time                : 0.531 s
% 0.72/0.89  # System time              : 0.019 s
% 0.72/0.89  # Total time               : 0.550 s
% 0.72/0.89  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
