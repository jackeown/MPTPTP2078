%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:40 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 902 expanded)
%              Number of clauses        :   68 ( 312 expanded)
%              Number of leaves         :   18 ( 218 expanded)
%              Depth                    :   15
%              Number of atoms          :  330 (4541 expanded)
%              Number of equality atoms :   17 (  50 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t21_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(t6_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( m1_connsp_2(X2,X1,X3)
               => r2_hidden(X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

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

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X47,X48,X49] :
      ( v2_struct_0(X47)
      | ~ v2_pre_topc(X47)
      | ~ l1_pre_topc(X47)
      | ~ m1_subset_1(X48,u1_struct_0(X47))
      | ~ m1_subset_1(X49,u1_struct_0(k9_yellow_6(X47,X48)))
      | m1_connsp_2(X49,X47,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_waybel_9])])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    & m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    & ~ m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_21,plain,(
    ! [X41,X42,X43] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | ~ m1_subset_1(X43,u1_struct_0(X41))
      | ~ m1_connsp_2(X42,X41,X43)
      | r2_hidden(X43,X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

fof(c_0_22,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | ~ m1_connsp_2(X40,X38,X39)
      | m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X23,X22)
        | r2_hidden(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ r2_hidden(X23,X22)
        | m1_subset_1(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ m1_subset_1(X23,X22)
        | v1_xboole_0(X23)
        | ~ v1_xboole_0(X22) )
      & ( ~ v1_xboole_0(X23)
        | m1_subset_1(X23,X22)
        | ~ v1_xboole_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_connsp_2(X1,esk2_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk2_0,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

fof(c_0_38,plain,(
    ! [X44,X45,X46] :
      ( ( r2_hidden(X45,X46)
        | ~ r2_hidden(X46,u1_struct_0(k9_yellow_6(X44,X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( v3_pre_topc(X46,X44)
        | ~ r2_hidden(X46,u1_struct_0(k9_yellow_6(X44,X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( ~ r2_hidden(X45,X46)
        | ~ v3_pre_topc(X46,X44)
        | r2_hidden(X46,u1_struct_0(k9_yellow_6(X44,X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_24]),c_0_25]),c_0_32])]),c_0_26])).

fof(c_0_43,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | k2_xboole_0(k1_tarski(X15),X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

fof(c_0_44,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_45,plain,(
    ! [X17,X18] : k3_tarski(k2_tarski(X17,X18)) = k2_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | ~ m1_subset_1(X29,k1_zfmisc_1(X27))
      | k4_subset_1(X27,X28,X29) = k2_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_51,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(k2_xboole_0(X9,X10),X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_46]),c_0_32])])).

fof(c_0_56,plain,(
    ! [X35,X36,X37] :
      ( ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ v3_pre_topc(X36,X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | ~ v3_pre_topc(X37,X35)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
      | v3_pre_topc(k2_xboole_0(X36,X37),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(esk2_0,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_37]),c_0_24]),c_0_25]),c_0_32])]),c_0_26])).

cnf(c_0_59,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X1,X1),X2)) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_55]),c_0_24]),c_0_25]),c_0_32])]),c_0_26])).

fof(c_0_64,plain,(
    ! [X12,X13] : r1_tarski(X12,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_65,plain,
    ( v3_pre_topc(k2_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_54])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_55]),c_0_24]),c_0_25]),c_0_32])]),c_0_26])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_60])).

fof(c_0_70,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | m1_subset_1(k4_subset_1(X24,X25,X26),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_61,c_0_54])).

cnf(c_0_72,negated_conjecture,
    ( k3_tarski(k2_tarski(k2_tarski(esk3_0,esk3_0),esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_74,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | m1_subset_1(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_75,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(X2,X3)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_54])).

cnf(c_0_76,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_60]),c_0_32])])).

cnf(c_0_77,negated_conjecture,
    ( k3_tarski(k2_tarski(X1,esk5_0)) = k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_58])).

cnf(c_0_78,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_46]),c_0_69])).

cnf(c_0_80,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_81,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,X21)
        | ~ r1_tarski(k2_tarski(X19,X20),X21) )
      & ( r2_hidden(X20,X21)
        | ~ r1_tarski(k2_tarski(X19,X20),X21) )
      & ( ~ r2_hidden(X19,X21)
        | ~ r2_hidden(X20,X21)
        | r1_tarski(k2_tarski(X19,X20),X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk3_0),X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_54])).

cnf(c_0_84,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_85,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( v3_pre_topc(k3_tarski(k2_tarski(X1,esk5_0)),esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_24]),c_0_25]),c_0_58])])).

cnf(c_0_87,negated_conjecture,
    ( k3_tarski(k2_tarski(esk4_0,esk5_0)) = k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_68])).

cnf(c_0_88,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_32])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_58])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk3_0),k3_tarski(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_92,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( v3_pre_topc(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_68]),c_0_87]),c_0_88])])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_68])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk3_0,k3_tarski(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_97,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | m1_subset_1(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,X1)))
    | ~ r2_hidden(X1,k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_24]),c_0_25]),c_0_94])]),c_0_26])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk3_0,k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_87])).

cnf(c_0_100,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(esk4_0,esk5_0)),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_96,c_0_54])).

cnf(c_0_101,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_100,c_0_87])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:59:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.40/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.40/0.58  # and selection function PSelectComplexPreferEQ.
% 0.40/0.58  #
% 0.40/0.58  # Preprocessing time       : 0.045 s
% 0.40/0.58  # Presaturation interreduction done
% 0.40/0.58  
% 0.40/0.58  # Proof found!
% 0.40/0.58  # SZS status Theorem
% 0.40/0.58  # SZS output start CNFRefutation
% 0.40/0.58  fof(t23_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 0.40/0.58  fof(t21_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_connsp_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 0.40/0.58  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.40/0.58  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.40/0.58  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.40/0.58  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.40/0.58  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 0.40/0.58  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.40/0.58  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.40/0.58  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.40/0.58  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.40/0.58  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.40/0.58  fof(fc7_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k2_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 0.40/0.58  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.40/0.58  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.40/0.58  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.40/0.58  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.40/0.58  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.40/0.58  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t23_waybel_9])).
% 0.40/0.58  fof(c_0_19, plain, ![X47, X48, X49]:(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)|(~m1_subset_1(X48,u1_struct_0(X47))|(~m1_subset_1(X49,u1_struct_0(k9_yellow_6(X47,X48)))|m1_connsp_2(X49,X47,X48)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_waybel_9])])])])).
% 0.40/0.58  fof(c_0_20, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))&(m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))&~m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.40/0.58  fof(c_0_21, plain, ![X41, X42, X43]:(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(~m1_subset_1(X43,u1_struct_0(X41))|(~m1_connsp_2(X42,X41,X43)|r2_hidden(X43,X42))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.40/0.58  fof(c_0_22, plain, ![X38, X39, X40]:(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|~m1_subset_1(X39,u1_struct_0(X38))|(~m1_connsp_2(X40,X38,X39)|m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.40/0.58  cnf(c_0_23, plain, (v2_struct_0(X1)|m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.40/0.58  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.58  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.58  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.58  fof(c_0_27, plain, ![X22, X23]:(((~m1_subset_1(X23,X22)|r2_hidden(X23,X22)|v1_xboole_0(X22))&(~r2_hidden(X23,X22)|m1_subset_1(X23,X22)|v1_xboole_0(X22)))&((~m1_subset_1(X23,X22)|v1_xboole_0(X23)|~v1_xboole_0(X22))&(~v1_xboole_0(X23)|m1_subset_1(X23,X22)|~v1_xboole_0(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.40/0.58  cnf(c_0_28, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.40/0.58  cnf(c_0_29, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.40/0.58  cnf(c_0_30, negated_conjecture, (m1_connsp_2(X1,esk2_0,X2)|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk2_0,X2)))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), c_0_26])).
% 0.40/0.58  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.58  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.58  cnf(c_0_33, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.40/0.58  cnf(c_0_34, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.40/0.58  fof(c_0_35, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.40/0.58  cnf(c_0_36, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.40/0.58  cnf(c_0_37, negated_conjecture, (m1_connsp_2(esk5_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.40/0.58  fof(c_0_38, plain, ![X44, X45, X46]:(((r2_hidden(X45,X46)|~r2_hidden(X46,u1_struct_0(k9_yellow_6(X44,X45)))|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44)))|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))&(v3_pre_topc(X46,X44)|~r2_hidden(X46,u1_struct_0(k9_yellow_6(X44,X45)))|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44)))|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(~r2_hidden(X45,X46)|~v3_pre_topc(X46,X44)|r2_hidden(X46,u1_struct_0(k9_yellow_6(X44,X45)))|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44)))|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 0.40/0.58  cnf(c_0_39, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.40/0.58  cnf(c_0_40, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))|v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.40/0.58  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.40/0.58  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_24]), c_0_25]), c_0_32])]), c_0_26])).
% 0.40/0.58  fof(c_0_43, plain, ![X15, X16]:(~r2_hidden(X15,X16)|k2_xboole_0(k1_tarski(X15),X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.40/0.58  fof(c_0_44, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.40/0.58  fof(c_0_45, plain, ![X17, X18]:k3_tarski(k2_tarski(X17,X18))=k2_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.40/0.58  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.58  cnf(c_0_47, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.40/0.58  fof(c_0_48, plain, ![X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|~m1_subset_1(X29,k1_zfmisc_1(X27))|k4_subset_1(X27,X28,X29)=k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.40/0.58  cnf(c_0_49, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.40/0.58  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.40/0.58  fof(c_0_51, plain, ![X9, X10, X11]:(~r1_tarski(k2_xboole_0(X9,X10),X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.40/0.58  cnf(c_0_52, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.40/0.58  cnf(c_0_53, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.40/0.58  cnf(c_0_54, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.40/0.58  cnf(c_0_55, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_46]), c_0_32])])).
% 0.40/0.58  fof(c_0_56, plain, ![X35, X36, X37]:(~v2_pre_topc(X35)|~l1_pre_topc(X35)|~v3_pre_topc(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~v3_pre_topc(X37,X35)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|v3_pre_topc(k2_xboole_0(X36,X37),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).
% 0.40/0.58  cnf(c_0_57, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,u1_struct_0(k9_yellow_6(esk2_0,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_24]), c_0_25])]), c_0_26])).
% 0.40/0.58  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_37]), c_0_24]), c_0_25]), c_0_32])]), c_0_26])).
% 0.40/0.58  cnf(c_0_59, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.40/0.58  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(sr,[status(thm)],[c_0_49, c_0_50])).
% 0.40/0.58  cnf(c_0_61, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.40/0.58  cnf(c_0_62, plain, (k3_tarski(k2_tarski(k2_tarski(X1,X1),X2))=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.40/0.58  cnf(c_0_63, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_55]), c_0_24]), c_0_25]), c_0_32])]), c_0_26])).
% 0.40/0.58  fof(c_0_64, plain, ![X12, X13]:r1_tarski(X12,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.40/0.58  cnf(c_0_65, plain, (v3_pre_topc(k2_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.40/0.58  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.40/0.58  cnf(c_0_67, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_59, c_0_54])).
% 0.40/0.58  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_55]), c_0_24]), c_0_25]), c_0_32])]), c_0_26])).
% 0.40/0.58  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_41, c_0_60])).
% 0.40/0.58  fof(c_0_70, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|~m1_subset_1(X26,k1_zfmisc_1(X24))|m1_subset_1(k4_subset_1(X24,X25,X26),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.40/0.58  cnf(c_0_71, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_61, c_0_54])).
% 0.40/0.58  cnf(c_0_72, negated_conjecture, (k3_tarski(k2_tarski(k2_tarski(esk3_0,esk3_0),esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.40/0.58  cnf(c_0_73, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.40/0.58  fof(c_0_74, plain, ![X32, X33, X34]:(~r2_hidden(X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(X34))|m1_subset_1(X32,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.40/0.58  cnf(c_0_75, plain, (v3_pre_topc(k3_tarski(k2_tarski(X2,X3)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_65, c_0_54])).
% 0.40/0.58  cnf(c_0_76, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_60]), c_0_32])])).
% 0.40/0.58  cnf(c_0_77, negated_conjecture, (k3_tarski(k2_tarski(X1,esk5_0))=k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_67, c_0_58])).
% 0.40/0.58  cnf(c_0_78, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_57, c_0_68])).
% 0.40/0.58  cnf(c_0_79, negated_conjecture, (r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_46]), c_0_69])).
% 0.40/0.58  cnf(c_0_80, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.40/0.58  fof(c_0_81, plain, ![X19, X20, X21]:(((r2_hidden(X19,X21)|~r1_tarski(k2_tarski(X19,X20),X21))&(r2_hidden(X20,X21)|~r1_tarski(k2_tarski(X19,X20),X21)))&(~r2_hidden(X19,X21)|~r2_hidden(X20,X21)|r1_tarski(k2_tarski(X19,X20),X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.40/0.58  cnf(c_0_82, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk3_0),X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.40/0.58  cnf(c_0_83, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_73, c_0_54])).
% 0.40/0.58  cnf(c_0_84, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.40/0.58  cnf(c_0_85, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.40/0.58  cnf(c_0_86, negated_conjecture, (v3_pre_topc(k3_tarski(k2_tarski(X1,esk5_0)),esk2_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_24]), c_0_25]), c_0_58])])).
% 0.40/0.58  cnf(c_0_87, negated_conjecture, (k3_tarski(k2_tarski(esk4_0,esk5_0))=k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_77, c_0_68])).
% 0.40/0.58  cnf(c_0_88, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_32])])).
% 0.40/0.58  cnf(c_0_89, negated_conjecture, (m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_80, c_0_58])).
% 0.40/0.58  cnf(c_0_90, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.40/0.58  cnf(c_0_91, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk3_0),k3_tarski(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.40/0.58  cnf(c_0_92, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_84, c_0_85])).
% 0.40/0.58  cnf(c_0_93, negated_conjecture, (v3_pre_topc(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_68]), c_0_87]), c_0_88])])).
% 0.40/0.58  cnf(c_0_94, negated_conjecture, (m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_89, c_0_68])).
% 0.40/0.58  cnf(c_0_95, negated_conjecture, (r2_hidden(esk3_0,k3_tarski(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.40/0.58  cnf(c_0_96, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.58  fof(c_0_97, plain, ![X30, X31]:(~r2_hidden(X30,X31)|m1_subset_1(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.40/0.58  cnf(c_0_98, negated_conjecture, (r2_hidden(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,X1)))|~r2_hidden(X1,k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_24]), c_0_25]), c_0_94])]), c_0_26])).
% 0.40/0.58  cnf(c_0_99, negated_conjecture, (r2_hidden(esk3_0,k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_95, c_0_87])).
% 0.40/0.58  cnf(c_0_100, negated_conjecture, (~m1_subset_1(k3_tarski(k2_tarski(esk4_0,esk5_0)),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_96, c_0_54])).
% 0.40/0.58  cnf(c_0_101, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.40/0.58  cnf(c_0_102, negated_conjecture, (r2_hidden(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.40/0.58  cnf(c_0_103, negated_conjecture, (~m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_100, c_0_87])).
% 0.40/0.58  cnf(c_0_104, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), ['proof']).
% 0.40/0.58  # SZS output end CNFRefutation
% 0.40/0.58  # Proof object total steps             : 105
% 0.40/0.58  # Proof object clause steps            : 68
% 0.40/0.58  # Proof object formula steps           : 37
% 0.40/0.58  # Proof object conjectures             : 45
% 0.40/0.58  # Proof object clause conjectures      : 42
% 0.40/0.58  # Proof object formula conjectures     : 3
% 0.40/0.58  # Proof object initial clauses used    : 26
% 0.40/0.58  # Proof object initial formulas used   : 18
% 0.40/0.58  # Proof object generating inferences   : 32
% 0.40/0.58  # Proof object simplifying inferences  : 59
% 0.40/0.58  # Training examples: 0 positive, 0 negative
% 0.40/0.58  # Parsed axioms                        : 18
% 0.40/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.58  # Initial clauses                      : 32
% 0.40/0.58  # Removed in clause preprocessing      : 2
% 0.40/0.58  # Initial clauses in saturation        : 30
% 0.40/0.58  # Processed clauses                    : 2537
% 0.40/0.58  # ...of these trivial                  : 222
% 0.40/0.58  # ...subsumed                          : 1077
% 0.40/0.58  # ...remaining for further processing  : 1238
% 0.40/0.58  # Other redundant clauses eliminated   : 0
% 0.40/0.58  # Clauses deleted for lack of memory   : 0
% 0.40/0.58  # Backward-subsumed                    : 5
% 0.40/0.58  # Backward-rewritten                   : 5
% 0.40/0.58  # Generated clauses                    : 6758
% 0.40/0.58  # ...of the previous two non-trivial   : 5790
% 0.40/0.58  # Contextual simplify-reflections      : 5
% 0.40/0.58  # Paramodulations                      : 6755
% 0.40/0.58  # Factorizations                       : 0
% 0.40/0.58  # Equation resolutions                 : 0
% 0.40/0.58  # Propositional unsat checks           : 0
% 0.40/0.58  #    Propositional check models        : 0
% 0.40/0.58  #    Propositional check unsatisfiable : 0
% 0.40/0.58  #    Propositional clauses             : 0
% 0.40/0.58  #    Propositional clauses after purity: 0
% 0.40/0.58  #    Propositional unsat core size     : 0
% 0.40/0.58  #    Propositional preprocessing time  : 0.000
% 0.40/0.58  #    Propositional encoding time       : 0.000
% 0.40/0.58  #    Propositional solver time         : 0.000
% 0.40/0.58  #    Success case prop preproc time    : 0.000
% 0.40/0.58  #    Success case prop encoding time   : 0.000
% 0.40/0.58  #    Success case prop solver time     : 0.000
% 0.40/0.58  # Current number of processed clauses  : 1196
% 0.40/0.58  #    Positive orientable unit clauses  : 589
% 0.40/0.58  #    Positive unorientable unit clauses: 0
% 0.40/0.58  #    Negative unit clauses             : 101
% 0.40/0.58  #    Non-unit-clauses                  : 506
% 0.40/0.58  # Current number of unprocessed clauses: 3297
% 0.40/0.58  # ...number of literals in the above   : 5876
% 0.40/0.58  # Current number of archived formulas  : 0
% 0.40/0.58  # Current number of archived clauses   : 44
% 0.40/0.58  # Clause-clause subsumption calls (NU) : 31737
% 0.40/0.58  # Rec. Clause-clause subsumption calls : 26573
% 0.40/0.58  # Non-unit clause-clause subsumptions  : 715
% 0.40/0.58  # Unit Clause-clause subsumption calls : 12268
% 0.40/0.58  # Rewrite failures with RHS unbound    : 0
% 0.40/0.58  # BW rewrite match attempts            : 2512
% 0.40/0.58  # BW rewrite match successes           : 8
% 0.40/0.58  # Condensation attempts                : 0
% 0.40/0.58  # Condensation successes               : 0
% 0.40/0.58  # Termbank termtop insertions          : 131213
% 0.42/0.58  
% 0.42/0.58  # -------------------------------------------------
% 0.42/0.58  # User time                : 0.217 s
% 0.42/0.58  # System time              : 0.011 s
% 0.42/0.58  # Total time               : 0.228 s
% 0.42/0.58  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
