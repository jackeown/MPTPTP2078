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
% DateTime   : Thu Dec  3 11:21:41 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 882 expanded)
%              Number of clauses        :   69 ( 305 expanded)
%              Number of leaves         :   16 ( 217 expanded)
%              Depth                    :   16
%              Number of atoms          :  342 (4472 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   22 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(fc7_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v3_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k2_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X18,X17)
        | r2_hidden(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ r2_hidden(X18,X17)
        | m1_subset_1(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ m1_subset_1(X18,X17)
        | v1_xboole_0(X18)
        | ~ v1_xboole_0(X17) )
      & ( ~ v1_xboole_0(X18)
        | m1_subset_1(X18,X17)
        | ~ v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    & m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    & ~ m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,u1_struct_0(X35))
      | ~ m1_connsp_2(X37,X35,X36)
      | m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_20,plain,(
    ! [X44,X45,X46] :
      ( v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | ~ m1_subset_1(X45,u1_struct_0(X44))
      | ~ m1_subset_1(X46,u1_struct_0(k9_yellow_6(X44,X45)))
      | m1_connsp_2(X46,X44,X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_waybel_9])])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,plain,(
    ! [X41,X42,X43] :
      ( ( r2_hidden(X42,X43)
        | ~ r2_hidden(X43,u1_struct_0(k9_yellow_6(X41,X42)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( v3_pre_topc(X43,X41)
        | ~ r2_hidden(X43,u1_struct_0(k9_yellow_6(X41,X42)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( ~ r2_hidden(X42,X43)
        | ~ v3_pre_topc(X43,X41)
        | r2_hidden(X43,u1_struct_0(k9_yellow_6(X41,X42)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    | r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_connsp_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_27]),c_0_28]),c_0_26])]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)),k1_xboole_0)
    | r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    | r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_27]),c_0_28]),c_0_26])]),c_0_29])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | m1_subset_1(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_27]),c_0_28]),c_0_39]),c_0_26])]),c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)),k1_xboole_0)
    | r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_41])).

fof(c_0_46,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | ~ m1_connsp_2(X39,X38,X40)
      | r2_hidden(X40,X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

cnf(c_0_47,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_22])])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | m1_subset_1(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_44]),c_0_27]),c_0_28]),c_0_45]),c_0_26])]),c_0_29])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_47])).

fof(c_0_51,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | ~ r1_tarski(X31,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_52,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_53,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k4_subset_1(X22,X23,X24) = k2_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_54,plain,(
    ! [X15,X16] : k3_tarski(k2_tarski(X15,X16)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_48]),c_0_22])])).

fof(c_0_56,plain,(
    ! [X32,X33,X34] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ v3_pre_topc(X33,X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ v3_pre_topc(X34,X32)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
      | v3_pre_topc(k2_xboole_0(X33,X34),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_22])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_55])).

fof(c_0_64,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_65,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | m1_subset_1(k4_subset_1(X19,X20,X21),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_66,plain,
    ( v3_pre_topc(k2_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ m1_connsp_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_68,negated_conjecture,
    ( m1_connsp_2(k1_xboole_0,esk2_0,esk3_0)
    | v3_pre_topc(esk5_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_58]),c_0_27]),c_0_28]),c_0_26])]),c_0_29])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_22])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_73,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | m1_subset_1(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_74,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(X2,X3)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_66,c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k3_tarski(k2_tarski(X1,esk5_0)) = k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_39])).

cnf(c_0_78,negated_conjecture,
    ( m1_connsp_2(k1_xboole_0,esk2_0,esk3_0)
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_71]),c_0_27]),c_0_28]),c_0_26])]),c_0_29])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_62])).

cnf(c_0_80,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_81,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( v3_pre_topc(k3_tarski(k2_tarski(X1,esk5_0)),esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_39]),c_0_27]),c_0_28])]),c_0_76])])).

cnf(c_0_84,negated_conjecture,
    ( k3_tarski(k2_tarski(esk4_0,esk5_0)) = k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_45])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_78]),c_0_69])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_35])).

cnf(c_0_88,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_45])).

cnf(c_0_90,negated_conjecture,
    ( v3_pre_topc(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_45]),c_0_84]),c_0_85])])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk3_0,k3_tarski(k2_tarski(X1,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_93,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | m1_subset_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,X1)))
    | ~ r2_hidden(X1,k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk3_0,k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_84])).

cnf(c_0_96,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(esk4_0,esk5_0)),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_92,c_0_62])).

cnf(c_0_97,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_96,c_0_84])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 16:52:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.21/0.36  # No SInE strategy applied
% 0.21/0.36  # Trying AutoSched0 for 299 seconds
% 0.40/0.58  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0S
% 0.40/0.58  # and selection function SelectComplexG.
% 0.40/0.58  #
% 0.40/0.58  # Preprocessing time       : 0.029 s
% 0.40/0.58  # Presaturation interreduction done
% 0.40/0.58  
% 0.40/0.58  # Proof found!
% 0.40/0.58  # SZS status Theorem
% 0.40/0.58  # SZS output start CNFRefutation
% 0.40/0.58  fof(t23_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_waybel_9)).
% 0.40/0.58  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.40/0.58  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.40/0.58  fof(t21_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_connsp_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_waybel_9)).
% 0.40/0.58  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.40/0.58  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 0.40/0.58  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.40/0.59  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.40/0.59  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.40/0.59  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.40/0.59  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.40/0.59  fof(fc7_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k2_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_tops_1)).
% 0.40/0.59  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.40/0.59  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.40/0.59  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.40/0.59  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.40/0.59  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t23_waybel_9])).
% 0.40/0.59  fof(c_0_17, plain, ![X17, X18]:(((~m1_subset_1(X18,X17)|r2_hidden(X18,X17)|v1_xboole_0(X17))&(~r2_hidden(X18,X17)|m1_subset_1(X18,X17)|v1_xboole_0(X17)))&((~m1_subset_1(X18,X17)|v1_xboole_0(X18)|~v1_xboole_0(X17))&(~v1_xboole_0(X18)|m1_subset_1(X18,X17)|~v1_xboole_0(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.40/0.59  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))&(m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))&~m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.40/0.59  fof(c_0_19, plain, ![X35, X36, X37]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_subset_1(X36,u1_struct_0(X35))|(~m1_connsp_2(X37,X35,X36)|m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.40/0.59  fof(c_0_20, plain, ![X44, X45, X46]:(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(~m1_subset_1(X45,u1_struct_0(X44))|(~m1_subset_1(X46,u1_struct_0(k9_yellow_6(X44,X45)))|m1_connsp_2(X46,X44,X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_waybel_9])])])])).
% 0.40/0.59  cnf(c_0_21, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.59  cnf(c_0_22, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.40/0.59  cnf(c_0_23, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.59  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.59  cnf(c_0_25, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.40/0.59  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.59  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.59  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.59  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.59  cnf(c_0_30, plain, (v2_struct_0(X1)|m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.59  fof(c_0_31, plain, ![X41, X42, X43]:(((r2_hidden(X42,X43)|~r2_hidden(X43,u1_struct_0(k9_yellow_6(X41,X42)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_subset_1(X42,u1_struct_0(X41))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(v3_pre_topc(X43,X41)|~r2_hidden(X43,u1_struct_0(k9_yellow_6(X41,X42)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_subset_1(X42,u1_struct_0(X41))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41))))&(~r2_hidden(X42,X43)|~v3_pre_topc(X43,X41)|r2_hidden(X43,u1_struct_0(k9_yellow_6(X41,X42)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_subset_1(X42,u1_struct_0(X41))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 0.40/0.59  cnf(c_0_32, plain, (m1_subset_1(X1,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.40/0.59  cnf(c_0_33, negated_conjecture, (v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))|r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.40/0.59  cnf(c_0_34, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_connsp_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.40/0.59  cnf(c_0_35, negated_conjecture, (m1_connsp_2(esk5_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_27]), c_0_28]), c_0_26])]), c_0_29])).
% 0.40/0.59  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.59  cnf(c_0_37, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.40/0.59  cnf(c_0_38, negated_conjecture, (m1_subset_1(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)),k1_xboole_0)|r2_hidden(esk5_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.40/0.59  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.40/0.59  cnf(c_0_40, negated_conjecture, (v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))|r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_23, c_0_36])).
% 0.40/0.59  cnf(c_0_41, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_36]), c_0_27]), c_0_28]), c_0_26])]), c_0_29])).
% 0.40/0.59  cnf(c_0_42, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.59  cnf(c_0_43, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|m1_subset_1(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_27]), c_0_28]), c_0_39]), c_0_26])]), c_0_29])).
% 0.40/0.59  cnf(c_0_44, negated_conjecture, (m1_subset_1(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)),k1_xboole_0)|r2_hidden(esk4_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_32, c_0_40])).
% 0.40/0.59  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_41])).
% 0.40/0.59  fof(c_0_46, plain, ![X38, X39, X40]:(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(~m1_subset_1(X40,u1_struct_0(X38))|(~m1_connsp_2(X39,X38,X40)|r2_hidden(X40,X39))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.40/0.59  cnf(c_0_47, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_22])])).
% 0.40/0.59  cnf(c_0_48, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|m1_subset_1(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_44]), c_0_27]), c_0_28]), c_0_45]), c_0_26])]), c_0_29])).
% 0.40/0.59  cnf(c_0_49, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.40/0.59  cnf(c_0_50, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_47])).
% 0.40/0.59  fof(c_0_51, plain, ![X30, X31]:(~r2_hidden(X30,X31)|~r1_tarski(X31,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.40/0.59  fof(c_0_52, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.40/0.59  fof(c_0_53, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|~m1_subset_1(X24,k1_zfmisc_1(X22))|k4_subset_1(X22,X23,X24)=k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.40/0.59  fof(c_0_54, plain, ![X15, X16]:k3_tarski(k2_tarski(X15,X16))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.40/0.59  cnf(c_0_55, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|v1_xboole_0(u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_48]), c_0_22])])).
% 0.40/0.59  fof(c_0_56, plain, ![X32, X33, X34]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|~v3_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~v3_pre_topc(X34,X32)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|v3_pre_topc(k2_xboole_0(X33,X34),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).
% 0.40/0.59  cnf(c_0_57, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_49, c_0_25])).
% 0.40/0.59  cnf(c_0_58, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_50, c_0_22])).
% 0.40/0.59  cnf(c_0_59, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.40/0.59  cnf(c_0_60, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.40/0.59  cnf(c_0_61, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.40/0.59  cnf(c_0_62, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.40/0.59  cnf(c_0_63, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_55])).
% 0.40/0.59  fof(c_0_64, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.40/0.59  fof(c_0_65, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|~m1_subset_1(X21,k1_zfmisc_1(X19))|m1_subset_1(k4_subset_1(X19,X20,X21),k1_zfmisc_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.40/0.59  cnf(c_0_66, plain, (v3_pre_topc(k2_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.40/0.59  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_0,X1)|~m1_connsp_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.40/0.59  cnf(c_0_68, negated_conjecture, (m1_connsp_2(k1_xboole_0,esk2_0,esk3_0)|v3_pre_topc(esk5_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_58]), c_0_27]), c_0_28]), c_0_26])]), c_0_29])).
% 0.40/0.59  cnf(c_0_69, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.40/0.59  cnf(c_0_70, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.40/0.59  cnf(c_0_71, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|m1_subset_1(k1_xboole_0,u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_63, c_0_22])).
% 0.40/0.59  cnf(c_0_72, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.40/0.59  fof(c_0_73, plain, ![X27, X28, X29]:(~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X29))|m1_subset_1(X27,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.40/0.59  cnf(c_0_74, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.40/0.59  cnf(c_0_75, plain, (v3_pre_topc(k3_tarski(k2_tarski(X2,X3)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_66, c_0_62])).
% 0.40/0.59  cnf(c_0_76, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.40/0.59  cnf(c_0_77, negated_conjecture, (k3_tarski(k2_tarski(X1,esk5_0))=k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_70, c_0_39])).
% 0.40/0.59  cnf(c_0_78, negated_conjecture, (m1_connsp_2(k1_xboole_0,esk2_0,esk3_0)|v3_pre_topc(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_71]), c_0_27]), c_0_28]), c_0_26])]), c_0_29])).
% 0.40/0.59  cnf(c_0_79, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k2_tarski(X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_62])).
% 0.40/0.59  cnf(c_0_80, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.40/0.59  cnf(c_0_81, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.40/0.59  cnf(c_0_82, negated_conjecture, (m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_74, c_0_39])).
% 0.40/0.59  cnf(c_0_83, negated_conjecture, (v3_pre_topc(k3_tarski(k2_tarski(X1,esk5_0)),esk2_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_39]), c_0_27]), c_0_28])]), c_0_76])])).
% 0.40/0.59  cnf(c_0_84, negated_conjecture, (k3_tarski(k2_tarski(esk4_0,esk5_0))=k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_77, c_0_45])).
% 0.40/0.59  cnf(c_0_85, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_78]), c_0_69])).
% 0.40/0.59  cnf(c_0_86, plain, (r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_79])).
% 0.40/0.59  cnf(c_0_87, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_67, c_0_35])).
% 0.40/0.59  cnf(c_0_88, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_80, c_0_81])).
% 0.40/0.59  cnf(c_0_89, negated_conjecture, (m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_82, c_0_45])).
% 0.40/0.59  cnf(c_0_90, negated_conjecture, (v3_pre_topc(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_45]), c_0_84]), c_0_85])])).
% 0.40/0.59  cnf(c_0_91, negated_conjecture, (r2_hidden(esk3_0,k3_tarski(k2_tarski(X1,esk5_0)))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.40/0.59  cnf(c_0_92, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.59  fof(c_0_93, plain, ![X25, X26]:(~r2_hidden(X25,X26)|m1_subset_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.40/0.59  cnf(c_0_94, negated_conjecture, (r2_hidden(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,X1)))|~r2_hidden(X1,k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_27]), c_0_28])]), c_0_29])).
% 0.40/0.59  cnf(c_0_95, negated_conjecture, (r2_hidden(esk3_0,k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_91, c_0_84])).
% 0.40/0.59  cnf(c_0_96, negated_conjecture, (~m1_subset_1(k3_tarski(k2_tarski(esk4_0,esk5_0)),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_92, c_0_62])).
% 0.40/0.59  cnf(c_0_97, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.40/0.59  cnf(c_0_98, negated_conjecture, (r2_hidden(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.40/0.59  cnf(c_0_99, negated_conjecture, (~m1_subset_1(k4_subset_1(u1_struct_0(esk2_0),esk4_0,esk5_0),u1_struct_0(k9_yellow_6(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_96, c_0_84])).
% 0.40/0.59  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99]), ['proof']).
% 0.40/0.59  # SZS output end CNFRefutation
% 0.40/0.59  # Proof object total steps             : 101
% 0.40/0.59  # Proof object clause steps            : 69
% 0.40/0.59  # Proof object formula steps           : 32
% 0.40/0.59  # Proof object conjectures             : 46
% 0.40/0.59  # Proof object clause conjectures      : 43
% 0.40/0.59  # Proof object formula conjectures     : 3
% 0.40/0.59  # Proof object initial clauses used    : 25
% 0.40/0.59  # Proof object initial formulas used   : 16
% 0.40/0.59  # Proof object generating inferences   : 37
% 0.40/0.59  # Proof object simplifying inferences  : 67
% 0.40/0.59  # Training examples: 0 positive, 0 negative
% 0.40/0.59  # Parsed axioms                        : 16
% 0.40/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.59  # Initial clauses                      : 32
% 0.40/0.59  # Removed in clause preprocessing      : 1
% 0.40/0.59  # Initial clauses in saturation        : 31
% 0.40/0.59  # Processed clauses                    : 770
% 0.40/0.59  # ...of these trivial                  : 41
% 0.40/0.59  # ...subsumed                          : 140
% 0.40/0.59  # ...remaining for further processing  : 589
% 0.40/0.59  # Other redundant clauses eliminated   : 108
% 0.40/0.59  # Clauses deleted for lack of memory   : 0
% 0.40/0.59  # Backward-subsumed                    : 14
% 0.40/0.59  # Backward-rewritten                   : 28
% 0.40/0.59  # Generated clauses                    : 8904
% 0.40/0.59  # ...of the previous two non-trivial   : 8383
% 0.40/0.59  # Contextual simplify-reflections      : 4
% 0.40/0.59  # Paramodulations                      : 8645
% 0.40/0.59  # Factorizations                       : 122
% 0.40/0.59  # Equation resolutions                 : 137
% 0.40/0.59  # Propositional unsat checks           : 0
% 0.40/0.59  #    Propositional check models        : 0
% 0.40/0.59  #    Propositional check unsatisfiable : 0
% 0.40/0.59  #    Propositional clauses             : 0
% 0.40/0.59  #    Propositional clauses after purity: 0
% 0.40/0.59  #    Propositional unsat core size     : 0
% 0.40/0.59  #    Propositional preprocessing time  : 0.000
% 0.40/0.59  #    Propositional encoding time       : 0.000
% 0.40/0.59  #    Propositional solver time         : 0.000
% 0.40/0.59  #    Success case prop preproc time    : 0.000
% 0.40/0.59  #    Success case prop encoding time   : 0.000
% 0.40/0.59  #    Success case prop solver time     : 0.000
% 0.40/0.59  # Current number of processed clauses  : 517
% 0.40/0.59  #    Positive orientable unit clauses  : 148
% 0.40/0.59  #    Positive unorientable unit clauses: 0
% 0.40/0.59  #    Negative unit clauses             : 3
% 0.40/0.59  #    Non-unit-clauses                  : 366
% 0.40/0.59  # Current number of unprocessed clauses: 7634
% 0.40/0.59  # ...number of literals in the above   : 44240
% 0.40/0.59  # Current number of archived formulas  : 0
% 0.40/0.59  # Current number of archived clauses   : 73
% 0.40/0.59  # Clause-clause subsumption calls (NU) : 18493
% 0.40/0.59  # Rec. Clause-clause subsumption calls : 11048
% 0.40/0.59  # Non-unit clause-clause subsumptions  : 148
% 0.40/0.59  # Unit Clause-clause subsumption calls : 3030
% 0.40/0.59  # Rewrite failures with RHS unbound    : 0
% 0.40/0.59  # BW rewrite match attempts            : 735
% 0.40/0.59  # BW rewrite match successes           : 13
% 0.40/0.59  # Condensation attempts                : 0
% 0.40/0.59  # Condensation successes               : 0
% 0.40/0.59  # Termbank termtop insertions          : 192631
% 0.40/0.59  
% 0.40/0.59  # -------------------------------------------------
% 0.40/0.59  # User time                : 0.220 s
% 0.40/0.59  # System time              : 0.006 s
% 0.40/0.59  # Total time               : 0.226 s
% 0.40/0.59  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
