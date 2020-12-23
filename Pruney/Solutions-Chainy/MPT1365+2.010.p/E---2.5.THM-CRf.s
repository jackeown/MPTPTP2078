%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:11 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 158 expanded)
%              Number of clauses        :   35 (  56 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  219 ( 835 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

fof(t29_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

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

fof(t19_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_compts_1(X2,X1)
                  & v2_compts_1(X3,X1) )
               => v2_compts_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_compts_1)).

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

fof(c_0_11,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | m1_subset_1(k9_subset_1(X12,X13,X14),k1_zfmisc_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_12,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | k9_subset_1(X18,X19,X20) = k3_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_13,plain,(
    ! [X26,X27,X28] :
      ( ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ v2_compts_1(X27,X26)
      | ~ r1_tarski(X28,X27)
      | ~ v4_pre_topc(X28,X26)
      | v2_compts_1(X28,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_compts_1])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] : r1_tarski(k3_xboole_0(X6,X7),k2_xboole_0(X6,X8)) ),
    inference(variable_rename,[status(thm)],[t29_xboole_1])).

fof(c_0_17,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X2,X1)
    | ~ r1_tarski(X3,X2)
    | ~ v4_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | m1_subset_1(k4_subset_1(X9,X10,X11),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
      | k4_subset_1(X15,X16,X17) = k2_xboole_0(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_24,plain,
    ( v2_compts_1(k3_xboole_0(X1,X2),X3)
    | ~ v2_compts_1(X4,X3)
    | ~ v4_pre_topc(k3_xboole_0(X1,X2),X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( v2_compts_1(k3_xboole_0(X1,X2),X3)
    | ~ v2_compts_1(k4_subset_1(u1_struct_0(X3),X4,X5),X3)
    | ~ v4_pre_topc(k3_xboole_0(X1,X2),X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(k3_xboole_0(X1,X2),k4_subset_1(u1_struct_0(X3),X4,X5)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k4_subset_1(X3,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_30,negated_conjecture,(
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

cnf(c_0_31,plain,
    ( v2_compts_1(k3_xboole_0(X1,X2),X3)
    | ~ v2_compts_1(k4_subset_1(u1_struct_0(X3),X2,X4),X3)
    | ~ v4_pre_topc(k3_xboole_0(X1,X2),X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v8_pre_topc(esk1_0)
    & v2_compts_1(esk2_0,esk1_0)
    & v2_compts_1(esk3_0,esk1_0)
    & ~ v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

fof(c_0_33,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ v2_compts_1(X30,X29)
      | ~ v2_compts_1(X31,X29)
      | v2_compts_1(k4_subset_1(u1_struct_0(X29),X30,X31),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_compts_1])])])).

cnf(c_0_34,plain,
    ( v2_compts_1(k3_xboole_0(X1,X2),X3)
    | ~ v2_compts_1(k2_xboole_0(X2,X4),X3)
    | ~ v4_pre_topc(k3_xboole_0(X1,X2),X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( v2_compts_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X2,X1)
    | ~ v2_compts_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X21,X22,X23] :
      ( ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ v4_pre_topc(X22,X21)
      | ~ v4_pre_topc(X23,X21)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X21),X22,X23),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_1])])])).

fof(c_0_40,plain,(
    ! [X24,X25] :
      ( ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v8_pre_topc(X24)
      | ~ v2_compts_1(X25,X24)
      | v4_pre_topc(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).

cnf(c_0_41,negated_conjecture,
    ( v2_compts_1(k3_xboole_0(X1,esk3_0),esk1_0)
    | ~ v2_compts_1(k2_xboole_0(esk3_0,X2),esk1_0)
    | ~ v4_pre_topc(k3_xboole_0(X1,esk3_0),esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_42,plain,
    ( v2_compts_1(k2_xboole_0(X1,X2),X3)
    | ~ v2_compts_1(X2,X3)
    | ~ v2_compts_1(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( v2_compts_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_compts_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( v8_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( v2_compts_1(k3_xboole_0(X1,esk3_0),esk1_0)
    | ~ v2_compts_1(X2,esk1_0)
    | ~ v4_pre_topc(k3_xboole_0(X1,esk3_0),esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_36]),c_0_35])])).

cnf(c_0_48,plain,
    ( v4_pre_topc(k3_xboole_0(X1,X2),X3)
    | ~ v4_pre_topc(X2,X3)
    | ~ v4_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_35]),c_0_43]),c_0_46]),c_0_36]),c_0_37])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( v2_compts_1(k3_xboole_0(X1,esk3_0),esk1_0)
    | ~ v2_compts_1(X2,esk1_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_36]),c_0_37]),c_0_35])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_compts_1(k3_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_15]),c_0_35])])).

cnf(c_0_55,negated_conjecture,
    ( v2_compts_1(k3_xboole_0(X1,esk3_0),esk1_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_35]),c_0_43])])).

cnf(c_0_56,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_52]),c_0_53]),c_0_46]),c_0_36]),c_0_37])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:24:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.12/0.37  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.013 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.12/0.37  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.12/0.37  fof(t18_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v2_compts_1(X2,X1)&r1_tarski(X3,X2))&v4_pre_topc(X3,X1))=>v2_compts_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 0.12/0.37  fof(t29_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 0.12/0.37  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.37  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.12/0.37  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.12/0.37  fof(t20_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v8_pre_topc(X1)&v2_compts_1(X2,X1))&v2_compts_1(X3,X1))=>v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 0.12/0.37  fof(t19_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_compts_1(X2,X1)&v2_compts_1(X3,X1))=>v2_compts_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_compts_1)).
% 0.12/0.37  fof(t35_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&v4_pre_topc(X3,X1))=>v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 0.12/0.37  fof(t16_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v8_pre_topc(X1)&v2_compts_1(X2,X1))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 0.12/0.37  fof(c_0_11, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|m1_subset_1(k9_subset_1(X12,X13,X14),k1_zfmisc_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.12/0.37  fof(c_0_12, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(X18))|k9_subset_1(X18,X19,X20)=k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.12/0.37  fof(c_0_13, plain, ![X26, X27, X28]:(~v2_pre_topc(X26)|~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~v2_compts_1(X27,X26)|~r1_tarski(X28,X27)|~v4_pre_topc(X28,X26)|v2_compts_1(X28,X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_compts_1])])])).
% 0.12/0.37  cnf(c_0_14, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_15, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_16, plain, ![X6, X7, X8]:r1_tarski(k3_xboole_0(X6,X7),k2_xboole_0(X6,X8)), inference(variable_rename,[status(thm)],[t29_xboole_1])).
% 0.12/0.37  fof(c_0_17, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.37  cnf(c_0_18, plain, (v2_compts_1(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_compts_1(X2,X1)|~r1_tarski(X3,X2)|~v4_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_19, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.37  fof(c_0_20, plain, ![X9, X10, X11]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|~m1_subset_1(X11,k1_zfmisc_1(X9))|m1_subset_1(k4_subset_1(X9,X10,X11),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.12/0.37  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_23, plain, ![X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|~m1_subset_1(X17,k1_zfmisc_1(X15))|k4_subset_1(X15,X16,X17)=k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.12/0.37  cnf(c_0_24, plain, (v2_compts_1(k3_xboole_0(X1,X2),X3)|~v2_compts_1(X4,X3)|~v4_pre_topc(k3_xboole_0(X1,X2),X3)|~l1_pre_topc(X3)|~v2_pre_topc(X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(k3_xboole_0(X1,X2),X4)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_25, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_26, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_27, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_28, plain, (v2_compts_1(k3_xboole_0(X1,X2),X3)|~v2_compts_1(k4_subset_1(u1_struct_0(X3),X4,X5),X3)|~v4_pre_topc(k3_xboole_0(X1,X2),X3)|~l1_pre_topc(X3)|~v2_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(k3_xboole_0(X1,X2),k4_subset_1(u1_struct_0(X3),X4,X5))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.37  cnf(c_0_29, plain, (r1_tarski(k3_xboole_0(X1,X2),k4_subset_1(X3,X2,X4))|~m1_subset_1(X4,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.37  fof(c_0_30, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v8_pre_topc(X1)&v2_compts_1(X2,X1))&v2_compts_1(X3,X1))=>v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t20_compts_1])).
% 0.12/0.37  cnf(c_0_31, plain, (v2_compts_1(k3_xboole_0(X1,X2),X3)|~v2_compts_1(k4_subset_1(u1_struct_0(X3),X2,X4),X3)|~v4_pre_topc(k3_xboole_0(X1,X2),X3)|~l1_pre_topc(X3)|~v2_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.37  fof(c_0_32, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((v8_pre_topc(esk1_0)&v2_compts_1(esk2_0,esk1_0))&v2_compts_1(esk3_0,esk1_0))&~v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.12/0.37  fof(c_0_33, plain, ![X29, X30, X31]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(~v2_compts_1(X30,X29)|~v2_compts_1(X31,X29)|v2_compts_1(k4_subset_1(u1_struct_0(X29),X30,X31),X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_compts_1])])])).
% 0.12/0.37  cnf(c_0_34, plain, (v2_compts_1(k3_xboole_0(X1,X2),X3)|~v2_compts_1(k2_xboole_0(X2,X4),X3)|~v4_pre_topc(k3_xboole_0(X1,X2),X3)|~l1_pre_topc(X3)|~v2_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_38, plain, (v2_compts_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_compts_1(X2,X1)|~v2_compts_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  fof(c_0_39, plain, ![X21, X22, X23]:(~v2_pre_topc(X21)|~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~v4_pre_topc(X22,X21)|~v4_pre_topc(X23,X21)|v4_pre_topc(k9_subset_1(u1_struct_0(X21),X22,X23),X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_1])])])).
% 0.12/0.37  fof(c_0_40, plain, ![X24, X25]:(~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~v8_pre_topc(X24)|~v2_compts_1(X25,X24)|v4_pre_topc(X25,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (v2_compts_1(k3_xboole_0(X1,esk3_0),esk1_0)|~v2_compts_1(k2_xboole_0(esk3_0,X2),esk1_0)|~v4_pre_topc(k3_xboole_0(X1,esk3_0),esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])])).
% 0.12/0.37  cnf(c_0_42, plain, (v2_compts_1(k2_xboole_0(X1,X2),X3)|~v2_compts_1(X2,X3)|~v2_compts_1(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_38, c_0_27])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (v2_compts_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_44, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v4_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_45, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v8_pre_topc(X1)|~v2_compts_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (v8_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (v2_compts_1(k3_xboole_0(X1,esk3_0),esk1_0)|~v2_compts_1(X2,esk1_0)|~v4_pre_topc(k3_xboole_0(X1,esk3_0),esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_36]), c_0_35])])).
% 0.12/0.37  cnf(c_0_48, plain, (v4_pre_topc(k3_xboole_0(X1,X2),X3)|~v4_pre_topc(X2,X3)|~v4_pre_topc(X1,X3)|~l1_pre_topc(X3)|~v2_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_44, c_0_15])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (v4_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_35]), c_0_43]), c_0_46]), c_0_36]), c_0_37])])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (~v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (v2_compts_1(k3_xboole_0(X1,esk3_0),esk1_0)|~v2_compts_1(X2,esk1_0)|~v4_pre_topc(X1,esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_36]), c_0_37]), c_0_35])])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (~v2_compts_1(k3_xboole_0(esk2_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_15]), c_0_35])])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (v2_compts_1(k3_xboole_0(X1,esk3_0),esk1_0)|~v4_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_35]), c_0_43])])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_52]), c_0_53]), c_0_46]), c_0_36]), c_0_37])])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_52])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 58
% 0.12/0.37  # Proof object clause steps            : 35
% 0.12/0.37  # Proof object formula steps           : 23
% 0.12/0.37  # Proof object conjectures             : 19
% 0.12/0.37  # Proof object clause conjectures      : 16
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 18
% 0.12/0.37  # Proof object initial formulas used   : 11
% 0.12/0.37  # Proof object generating inferences   : 17
% 0.12/0.37  # Proof object simplifying inferences  : 29
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 11
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 18
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 18
% 0.12/0.37  # Processed clauses                    : 355
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 218
% 0.12/0.37  # ...remaining for further processing  : 136
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 3
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 605
% 0.12/0.37  # ...of the previous two non-trivial   : 535
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 605
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 115
% 0.12/0.37  #    Positive orientable unit clauses  : 11
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 99
% 0.12/0.37  # Current number of unprocessed clauses: 216
% 0.12/0.37  # ...number of literals in the above   : 1371
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 21
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 7391
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 1953
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 215
% 0.12/0.37  # Unit Clause-clause subsumption calls : 87
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 3
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 17959
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.024 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.028 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
