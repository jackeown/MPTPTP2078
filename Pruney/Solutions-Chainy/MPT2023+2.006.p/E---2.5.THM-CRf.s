%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:38 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 727 expanded)
%              Number of clauses        :   49 ( 232 expanded)
%              Number of leaves         :   14 ( 180 expanded)
%              Depth                    :   11
%              Number of atoms          :  310 (3856 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_waybel_9,conjecture,(
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
                 => m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(redefinition_k8_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(dt_k8_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k8_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc6_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v3_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k3_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_14,negated_conjecture,(
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
                   => m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_waybel_9])).

fof(c_0_15,plain,(
    ! [X45,X46,X47] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,u1_struct_0(X45))
      | ~ m1_subset_1(X47,u1_struct_0(k9_yellow_6(X45,X46)))
      | m1_connsp_2(X47,X45,X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_waybel_9])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    & m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    & ~ m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | ~ m1_connsp_2(X38,X36,X37)
      | m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X42,X43,X44] :
      ( ( r2_hidden(X43,X44)
        | ~ r2_hidden(X44,u1_struct_0(k9_yellow_6(X42,X43)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( v3_pre_topc(X44,X42)
        | ~ r2_hidden(X44,u1_struct_0(k9_yellow_6(X42,X43)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( ~ r2_hidden(X43,X44)
        | ~ v3_pre_topc(X44,X42)
        | r2_hidden(X44,u1_struct_0(k9_yellow_6(X42,X43)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

fof(c_0_25,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | m1_subset_1(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_26,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | ~ m1_subset_1(X41,u1_struct_0(X39))
      | ~ m1_connsp_2(X40,X39,X41)
      | r2_hidden(X41,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( m1_connsp_2(esk6_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_29,plain,(
    ! [X26,X27] : k1_setfam_1(k2_tarski(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_30,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | m1_subset_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_31,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k8_subset_1(X23,X24,X25) = k3_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_subset_1])])).

fof(c_0_34,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X19,X18)
        | r2_hidden(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ r2_hidden(X19,X18)
        | m1_subset_1(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ m1_subset_1(X19,X18)
        | v1_xboole_0(X19)
        | ~ v1_xboole_0(X18) )
      & ( ~ v1_xboole_0(X19)
        | m1_subset_1(X19,X18)
        | ~ v1_xboole_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_42,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | m1_subset_1(k8_subset_1(X20,X21,X22),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_subset_1])])).

cnf(c_0_43,plain,
    ( k8_subset_1(X2,X1,X3) = k3_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_46,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ m1_connsp_2(esk6_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_20]),c_0_21])]),c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_37]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( m1_subset_1(k8_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k8_subset_1(X2,X1,X3) = k1_setfam_1(k2_tarski(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_39])).

fof(c_0_53,plain,(
    ! [X33,X34,X35] :
      ( ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ v3_pre_topc(X34,X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ v3_pre_topc(X35,X33)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
      | v3_pre_topc(k3_xboole_0(X34,X35),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X2,X1)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_22])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_48]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_59,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),esk3_0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk4_0,k1_setfam_1(k2_tarski(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_20]),c_0_21])]),c_0_23])).

cnf(c_0_61,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( v3_pre_topc(k3_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk3_0)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_19]),c_0_20]),c_0_21]),c_0_36]),c_0_22])]),c_0_23])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_37]),c_0_20]),c_0_21]),c_0_58]),c_0_22])]),c_0_23])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),esk3_0)
    | ~ r2_hidden(esk4_0,k1_setfam_1(k2_tarski(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_58])])).

cnf(c_0_69,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(X2,X3)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_39])).

cnf(c_0_70,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_66]),c_0_65])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_tarski(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_67,c_0_39])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ m1_connsp_2(esk5_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_58]),c_0_20]),c_0_21])]),c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_setfam_1(k2_tarski(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71]),c_0_20]),c_0_21]),c_0_36]),c_0_58])])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_48]),c_0_22])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_57]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:03:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.014 s
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t22_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_waybel_9)).
% 0.12/0.36  fof(t21_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_connsp_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 0.12/0.36  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.12/0.36  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 0.12/0.36  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.36  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.12/0.36  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.36  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.12/0.36  fof(redefinition_k8_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_subset_1)).
% 0.12/0.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.12/0.36  fof(dt_k8_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k8_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_subset_1)).
% 0.12/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.36  fof(fc6_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k3_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_tops_1)).
% 0.12/0.36  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.12/0.36  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t22_waybel_9])).
% 0.12/0.36  fof(c_0_15, plain, ![X45, X46, X47]:(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~m1_subset_1(X46,u1_struct_0(X45))|(~m1_subset_1(X47,u1_struct_0(k9_yellow_6(X45,X46)))|m1_connsp_2(X47,X45,X46)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_waybel_9])])])])).
% 0.12/0.36  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))&(m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))&~m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.12/0.36  fof(c_0_17, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|~m1_subset_1(X37,u1_struct_0(X36))|(~m1_connsp_2(X38,X36,X37)|m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.12/0.36  cnf(c_0_18, plain, (v2_struct_0(X1)|m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  fof(c_0_24, plain, ![X42, X43, X44]:(((r2_hidden(X43,X44)|~r2_hidden(X44,u1_struct_0(k9_yellow_6(X42,X43)))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~m1_subset_1(X43,u1_struct_0(X42))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))&(v3_pre_topc(X44,X42)|~r2_hidden(X44,u1_struct_0(k9_yellow_6(X42,X43)))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~m1_subset_1(X43,u1_struct_0(X42))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))))&(~r2_hidden(X43,X44)|~v3_pre_topc(X44,X42)|r2_hidden(X44,u1_struct_0(k9_yellow_6(X42,X43)))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~m1_subset_1(X43,u1_struct_0(X42))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 0.12/0.36  fof(c_0_25, plain, ![X30, X31, X32]:(~r2_hidden(X30,X31)|~m1_subset_1(X31,k1_zfmisc_1(X32))|m1_subset_1(X30,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.36  fof(c_0_26, plain, ![X39, X40, X41]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(~m1_subset_1(X41,u1_struct_0(X39))|(~m1_connsp_2(X40,X39,X41)|r2_hidden(X41,X40))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.12/0.36  cnf(c_0_27, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_28, negated_conjecture, (m1_connsp_2(esk6_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.36  fof(c_0_29, plain, ![X26, X27]:k1_setfam_1(k2_tarski(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.36  fof(c_0_30, plain, ![X28, X29]:(~r2_hidden(X28,X29)|m1_subset_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.12/0.36  cnf(c_0_31, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.36  cnf(c_0_32, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.36  fof(c_0_33, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|k8_subset_1(X23,X24,X25)=k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_subset_1])])).
% 0.12/0.36  fof(c_0_34, plain, ![X18, X19]:(((~m1_subset_1(X19,X18)|r2_hidden(X19,X18)|v1_xboole_0(X18))&(~r2_hidden(X19,X18)|m1_subset_1(X19,X18)|v1_xboole_0(X18)))&((~m1_subset_1(X19,X18)|v1_xboole_0(X19)|~v1_xboole_0(X18))&(~v1_xboole_0(X19)|m1_subset_1(X19,X18)|~v1_xboole_0(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.12/0.36  cnf(c_0_35, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.36  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.36  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (~m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  cnf(c_0_40, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.36  cnf(c_0_41, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.36  fof(c_0_42, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|m1_subset_1(k8_subset_1(X20,X21,X22),k1_zfmisc_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_subset_1])])).
% 0.12/0.36  cnf(c_0_43, plain, (k8_subset_1(X2,X1,X3)=k3_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.36  cnf(c_0_44, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.36  cnf(c_0_45, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.36  fof(c_0_46, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.36  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,esk6_0)|~m1_connsp_2(esk6_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_20]), c_0_21])]), c_0_23])).
% 0.12/0.36  cnf(c_0_48, negated_conjecture, (m1_connsp_2(esk5_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_37]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.36  cnf(c_0_49, negated_conjecture, (~m1_subset_1(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.36  cnf(c_0_50, plain, (v2_struct_0(X1)|m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.36  cnf(c_0_51, plain, (m1_subset_1(k8_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.36  cnf(c_0_52, plain, (k8_subset_1(X2,X1,X3)=k1_setfam_1(k2_tarski(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_43, c_0_39])).
% 0.12/0.36  fof(c_0_53, plain, ![X33, X34, X35]:(~v2_pre_topc(X33)|~l1_pre_topc(X33)|~v3_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~v3_pre_topc(X35,X33)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|v3_pre_topc(k3_xboole_0(X34,X35),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).
% 0.12/0.36  cnf(c_0_54, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.36  cnf(c_0_55, plain, (v2_struct_0(X1)|v3_pre_topc(X2,X1)|v1_xboole_0(u1_struct_0(k9_yellow_6(X1,X3)))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.12/0.36  cnf(c_0_56, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.36  cnf(c_0_57, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_22])])).
% 0.12/0.36  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_48]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.36  fof(c_0_59, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10))&(r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k3_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|~r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k3_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))&(r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.12/0.36  cnf(c_0_60, negated_conjecture, (~v3_pre_topc(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),esk3_0)|~m1_subset_1(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk4_0,k1_setfam_1(k2_tarski(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_20]), c_0_21])]), c_0_23])).
% 0.12/0.36  cnf(c_0_61, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.36  cnf(c_0_62, plain, (v3_pre_topc(k3_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.36  cnf(c_0_63, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_54, c_0_19])).
% 0.12/0.36  cnf(c_0_64, negated_conjecture, (v3_pre_topc(esk6_0,esk3_0)|v1_xboole_0(u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_19]), c_0_20]), c_0_21]), c_0_36]), c_0_22])]), c_0_23])).
% 0.12/0.36  cnf(c_0_65, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.36  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)|v1_xboole_0(u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_37]), c_0_20]), c_0_21]), c_0_58]), c_0_22])]), c_0_23])).
% 0.12/0.36  cnf(c_0_67, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.12/0.36  cnf(c_0_68, negated_conjecture, (~v3_pre_topc(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),esk3_0)|~r2_hidden(esk4_0,k1_setfam_1(k2_tarski(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_58])])).
% 0.12/0.36  cnf(c_0_69, plain, (v3_pre_topc(k1_setfam_1(k2_tarski(X2,X3)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_62, c_0_39])).
% 0.12/0.36  cnf(c_0_70, negated_conjecture, (v3_pre_topc(esk6_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.12/0.36  cnf(c_0_71, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_66]), c_0_65])).
% 0.12/0.36  cnf(c_0_72, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_tarski(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_67, c_0_39])).
% 0.12/0.36  cnf(c_0_73, negated_conjecture, (r2_hidden(X1,esk5_0)|~m1_connsp_2(esk5_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_58]), c_0_20]), c_0_21])]), c_0_23])).
% 0.12/0.36  cnf(c_0_74, negated_conjecture, (~r2_hidden(esk4_0,k1_setfam_1(k2_tarski(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71]), c_0_20]), c_0_21]), c_0_36]), c_0_58])])).
% 0.12/0.36  cnf(c_0_75, plain, (r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_72])).
% 0.12/0.36  cnf(c_0_76, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_48]), c_0_22])])).
% 0.12/0.36  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_57]), c_0_76])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 78
% 0.12/0.36  # Proof object clause steps            : 49
% 0.12/0.36  # Proof object formula steps           : 29
% 0.12/0.36  # Proof object conjectures             : 29
% 0.12/0.36  # Proof object clause conjectures      : 26
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 22
% 0.12/0.36  # Proof object initial formulas used   : 14
% 0.12/0.36  # Proof object generating inferences   : 21
% 0.12/0.36  # Proof object simplifying inferences  : 68
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 14
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 31
% 0.12/0.36  # Removed in clause preprocessing      : 1
% 0.12/0.36  # Initial clauses in saturation        : 30
% 0.12/0.36  # Processed clauses                    : 208
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 81
% 0.12/0.36  # ...remaining for further processing  : 127
% 0.12/0.36  # Other redundant clauses eliminated   : 3
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 3
% 0.12/0.36  # Backward-rewritten                   : 4
% 0.12/0.36  # Generated clauses                    : 507
% 0.12/0.36  # ...of the previous two non-trivial   : 455
% 0.12/0.36  # Contextual simplify-reflections      : 4
% 0.12/0.36  # Paramodulations                      : 500
% 0.12/0.36  # Factorizations                       : 4
% 0.12/0.36  # Equation resolutions                 : 3
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 117
% 0.12/0.36  #    Positive orientable unit clauses  : 15
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 5
% 0.12/0.36  #    Non-unit-clauses                  : 97
% 0.12/0.36  # Current number of unprocessed clauses: 250
% 0.12/0.36  # ...number of literals in the above   : 1186
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 8
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 1656
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 845
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 76
% 0.12/0.36  # Unit Clause-clause subsumption calls : 109
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 2
% 0.12/0.36  # BW rewrite match successes           : 2
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 11191
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.024 s
% 0.12/0.36  # System time              : 0.001 s
% 0.12/0.36  # Total time               : 0.025 s
% 0.12/0.36  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
