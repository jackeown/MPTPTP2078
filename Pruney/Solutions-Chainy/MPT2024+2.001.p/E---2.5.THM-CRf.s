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
% DateTime   : Thu Dec  3 11:21:39 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 504 expanded)
%              Number of clauses        :   55 ( 172 expanded)
%              Number of leaves         :   13 ( 123 expanded)
%              Depth                    :   14
%              Number of atoms          :  255 (2774 expanded)
%              Number of equality atoms :   14 (  73 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))
                 => m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

fof(t38_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => ? [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                  & X4 = X3
                  & r2_hidden(X2,X4)
                  & v3_pre_topc(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(fc7_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v3_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k2_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t39_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))
              <=> ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))
                   => m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_waybel_9])).

fof(c_0_14,plain,(
    ! [X29,X30,X31] :
      ( ( m1_subset_1(esk1_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( esk1_3(X29,X30,X31) = X31
        | ~ m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( r2_hidden(X30,esk1_3(X29,X30,X31))
        | ~ m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v3_pre_topc(esk1_3(X29,X30,X31),X29)
        | ~ m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    & m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    & ~ m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_16,plain,
    ( esk1_3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( esk1_3(esk2_0,X1,X2) = X2
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(esk2_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_24,plain,(
    ! [X9,X10] : r1_tarski(X9,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( esk1_3(esk2_0,esk3_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | m1_subset_1(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | r1_tarski(k2_xboole_0(X11,X13),k2_xboole_0(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_17]),c_0_18]),c_0_21]),c_0_22])]),c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( esk1_3(esk2_0,esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_27]),c_0_22])])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,esk1_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_38,plain,(
    ! [X26,X27,X28] :
      ( ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ v3_pre_topc(X27,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ v3_pre_topc(X28,X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | v3_pre_topc(k2_xboole_0(X27,X28),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).

cnf(c_0_39,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_42,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_43,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k2_xboole_0(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34]),c_0_17]),c_0_18]),c_0_27]),c_0_22])]),c_0_19])).

fof(c_0_45,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_46,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X16,X17)
      | v1_xboole_0(X17)
      | r2_hidden(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_17]),c_0_18]),c_0_21]),c_0_22])]),c_0_19])).

cnf(c_0_49,plain,
    ( v3_pre_topc(k2_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_17]),c_0_18]),c_0_21]),c_0_22])]),c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk5_0,X1),k2_xboole_0(u1_struct_0(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_44])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_58,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X34,X35)
        | ~ r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v3_pre_topc(X35,X33)
        | ~ r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r2_hidden(X34,X35)
        | ~ v3_pre_topc(X35,X33)
        | r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(k2_xboole_0(X1,esk5_0),esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_17]),c_0_18])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk5_0,X1),k2_xboole_0(X1,u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(esk4_0,u1_struct_0(esk2_0)) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( ~ v1_xboole_0(k2_xboole_0(X1,X2))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_36])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(esk5_0,X1))
    | r2_hidden(esk3_0,k2_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( v3_pre_topc(k2_xboole_0(X1,esk5_0),esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_33])])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_17]),c_0_18]),c_0_27]),c_0_22])]),c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(esk5_0,X1))
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_64,c_0_35])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(k2_xboole_0(esk4_0,esk5_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_44]),c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_48])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_69])).

fof(c_0_75,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | m1_subset_1(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,X1)))
    | ~ r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_17]),c_0_18])]),c_0_19]),c_0_72])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:25:11 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.18/0.38  # and selection function PSelectComplexPreferEQ.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.028 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t23_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 0.18/0.38  fof(t38_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&X4=X3)&r2_hidden(X2,X4))&v3_pre_topc(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_6)).
% 0.18/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.18/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.18/0.38  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 0.18/0.38  fof(fc7_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k2_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 0.18/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.18/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.18/0.38  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 0.18/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.18/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t23_waybel_9])).
% 0.18/0.38  fof(c_0_14, plain, ![X29, X30, X31]:((((m1_subset_1(esk1_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))|~m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(esk1_3(X29,X30,X31)=X31|~m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))))&(r2_hidden(X30,esk1_3(X29,X30,X31))|~m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))))&(v3_pre_topc(esk1_3(X29,X30,X31),X29)|~m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).
% 0.18/0.38  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))&(m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))&~m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.18/0.38  cnf(c_0_16, plain, (esk1_3(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.38  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_20, negated_conjecture, (esk1_3(esk2_0,X1,X2)=X2|~m1_subset_1(X2,u1_struct_0(k9_yellow_6(esk2_0,X1)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), c_0_19])).
% 0.18/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  fof(c_0_23, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.38  fof(c_0_24, plain, ![X9, X10]:r1_tarski(X9,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.18/0.38  cnf(c_0_25, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.38  cnf(c_0_26, negated_conjecture, (esk1_3(esk2_0,esk3_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.18/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  fof(c_0_28, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|m1_subset_1(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.18/0.38  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.38  fof(c_0_31, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|r1_tarski(k2_xboole_0(X11,X13),k2_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 0.18/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_17]), c_0_18]), c_0_21]), c_0_22])]), c_0_19])).
% 0.18/0.38  cnf(c_0_34, negated_conjecture, (esk1_3(esk2_0,esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_27]), c_0_22])])).
% 0.18/0.38  cnf(c_0_35, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.38  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.38  cnf(c_0_37, plain, (r2_hidden(X1,esk1_3(X2,X1,X3))|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.38  fof(c_0_38, plain, ![X26, X27, X28]:(~v2_pre_topc(X26)|~l1_pre_topc(X26)|~v3_pre_topc(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~v3_pre_topc(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|v3_pre_topc(k2_xboole_0(X27,X28),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).
% 0.18/0.38  cnf(c_0_39, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.38  cnf(c_0_40, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.38  cnf(c_0_41, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.18/0.38  fof(c_0_42, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.38  fof(c_0_43, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k2_xboole_0(X7,X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_34]), c_0_17]), c_0_18]), c_0_27]), c_0_22])]), c_0_19])).
% 0.18/0.38  fof(c_0_45, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|~v1_xboole_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.18/0.38  fof(c_0_46, plain, ![X16, X17]:(~m1_subset_1(X16,X17)|(v1_xboole_0(X17)|r2_hidden(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.18/0.38  cnf(c_0_47, plain, (m1_subset_1(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_17]), c_0_18]), c_0_21]), c_0_22])]), c_0_19])).
% 0.18/0.38  cnf(c_0_49, plain, (v3_pre_topc(k2_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.38  cnf(c_0_50, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_17]), c_0_18]), c_0_21]), c_0_22])]), c_0_19])).
% 0.18/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(k2_xboole_0(esk5_0,X1),k2_xboole_0(u1_struct_0(esk2_0),X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.38  cnf(c_0_52, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.38  cnf(c_0_53, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_44])).
% 0.18/0.38  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.38  cnf(c_0_56, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.38  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk3_0,k2_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.38  fof(c_0_58, plain, ![X33, X34, X35]:(((r2_hidden(X34,X35)|~r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(v3_pre_topc(X35,X33)|~r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(~r2_hidden(X34,X35)|~v3_pre_topc(X35,X33)|r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 0.18/0.38  cnf(c_0_59, negated_conjecture, (v3_pre_topc(k2_xboole_0(X1,esk5_0),esk2_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_17]), c_0_18])])).
% 0.18/0.38  cnf(c_0_60, negated_conjecture, (r1_tarski(k2_xboole_0(esk5_0,X1),k2_xboole_0(X1,u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.38  cnf(c_0_61, negated_conjecture, (k2_xboole_0(esk4_0,u1_struct_0(esk2_0))=u1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.18/0.38  cnf(c_0_62, plain, (~v1_xboole_0(k2_xboole_0(X1,X2))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_55, c_0_36])).
% 0.18/0.38  cnf(c_0_63, negated_conjecture, (v1_xboole_0(k2_xboole_0(esk5_0,X1))|r2_hidden(esk3_0,k2_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.38  cnf(c_0_64, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.38  cnf(c_0_65, negated_conjecture, (v3_pre_topc(k2_xboole_0(X1,esk5_0),esk2_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_33])])).
% 0.18/0.38  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_17]), c_0_18]), c_0_27]), c_0_22])]), c_0_19])).
% 0.18/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_52])).
% 0.18/0.38  cnf(c_0_68, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(esk5_0,X1))|~r2_hidden(X2,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.18/0.38  cnf(c_0_69, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 0.18/0.38  cnf(c_0_70, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_64, c_0_35])).
% 0.18/0.38  cnf(c_0_71, negated_conjecture, (v3_pre_topc(k2_xboole_0(esk4_0,esk5_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_44]), c_0_66])])).
% 0.18/0.38  cnf(c_0_72, negated_conjecture, (m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_29, c_0_67])).
% 0.18/0.38  cnf(c_0_73, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_68, c_0_48])).
% 0.18/0.38  cnf(c_0_74, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_53, c_0_69])).
% 0.18/0.38  fof(c_0_75, plain, ![X14, X15]:(~r2_hidden(X14,X15)|m1_subset_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.18/0.38  cnf(c_0_76, negated_conjecture, (r2_hidden(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,X1)))|~r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_17]), c_0_18])]), c_0_19]), c_0_72])])).
% 0.18/0.38  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.18/0.38  cnf(c_0_78, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.18/0.38  cnf(c_0_79, negated_conjecture, (r2_hidden(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.18/0.38  cnf(c_0_80, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 82
% 0.18/0.38  # Proof object clause steps            : 55
% 0.18/0.38  # Proof object formula steps           : 27
% 0.18/0.38  # Proof object conjectures             : 36
% 0.18/0.38  # Proof object clause conjectures      : 33
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 23
% 0.18/0.38  # Proof object initial formulas used   : 13
% 0.18/0.38  # Proof object generating inferences   : 30
% 0.18/0.38  # Proof object simplifying inferences  : 53
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 13
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 25
% 0.18/0.38  # Removed in clause preprocessing      : 0
% 0.18/0.38  # Initial clauses in saturation        : 25
% 0.18/0.38  # Processed clauses                    : 510
% 0.18/0.38  # ...of these trivial                  : 59
% 0.18/0.38  # ...subsumed                          : 215
% 0.18/0.38  # ...remaining for further processing  : 236
% 0.18/0.38  # Other redundant clauses eliminated   : 0
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 5
% 0.18/0.38  # Backward-rewritten                   : 10
% 0.18/0.38  # Generated clauses                    : 1517
% 0.18/0.38  # ...of the previous two non-trivial   : 939
% 0.18/0.38  # Contextual simplify-reflections      : 1
% 0.18/0.38  # Paramodulations                      : 1517
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 0
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 196
% 0.18/0.38  #    Positive orientable unit clauses  : 103
% 0.18/0.38  #    Positive unorientable unit clauses: 1
% 0.18/0.38  #    Negative unit clauses             : 9
% 0.18/0.38  #    Non-unit-clauses                  : 83
% 0.18/0.38  # Current number of unprocessed clauses: 461
% 0.18/0.38  # ...number of literals in the above   : 712
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 40
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 2586
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 1537
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 187
% 0.18/0.38  # Unit Clause-clause subsumption calls : 695
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 56
% 0.18/0.38  # BW rewrite match successes           : 17
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 20577
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.051 s
% 0.18/0.38  # System time              : 0.006 s
% 0.18/0.38  # Total time               : 0.058 s
% 0.18/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
