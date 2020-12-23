%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:38 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 633 expanded)
%              Number of clauses        :   51 ( 216 expanded)
%              Number of leaves         :   15 ( 158 expanded)
%              Depth                    :   10
%              Number of atoms          :  316 (3166 expanded)
%              Number of equality atoms :   20 (  65 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc6_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v3_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k3_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    & m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    & ~ m1_subset_1(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_17,plain,(
    ! [X34,X35] : k1_setfam_1(k2_tarski(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_19,plain,(
    ! [X47,X48,X49] :
      ( ( r2_hidden(X48,X49)
        | ~ r2_hidden(X49,u1_struct_0(k9_yellow_6(X47,X48)))
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) )
      & ( v3_pre_topc(X49,X47)
        | ~ r2_hidden(X49,u1_struct_0(k9_yellow_6(X47,X48)))
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) )
      & ( ~ r2_hidden(X48,X49)
        | ~ v3_pre_topc(X49,X47)
        | r2_hidden(X49,u1_struct_0(k9_yellow_6(X47,X48)))
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

fof(c_0_20,plain,(
    ! [X38,X39,X40] :
      ( ~ r2_hidden(X38,X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(X40))
      | m1_subset_1(X38,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_21,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_25,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_26,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | m1_subset_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_27,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X31))
      | k9_subset_1(X31,X32,X33) = k3_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_30,plain,(
    ! [X50,X51,X52] :
      ( v2_struct_0(X50)
      | ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,u1_struct_0(X50))
      | ~ m1_subset_1(X52,u1_struct_0(k9_yellow_6(X50,X51)))
      | m1_connsp_2(X52,X50,X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_waybel_9])])])])).

cnf(c_0_31,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_38,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X28))
      | m1_subset_1(k9_subset_1(X28,X29,X30),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_39,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X44,X45,X46] :
      ( v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | ~ m1_subset_1(X45,u1_struct_0(X44))
      | ~ m1_connsp_2(X46,X44,X45)
      | m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_47,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X27,X26)
        | r2_hidden(X27,X26)
        | v1_xboole_0(X26) )
      & ( ~ r2_hidden(X27,X26)
        | m1_subset_1(X27,X26)
        | v1_xboole_0(X26) )
      & ( ~ m1_subset_1(X27,X26)
        | v1_xboole_0(X27)
        | ~ v1_xboole_0(X26) )
      & ( ~ v1_xboole_0(X27)
        | m1_subset_1(X27,X26)
        | ~ v1_xboole_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_51,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( m1_connsp_2(esk7_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_46])).

fof(c_0_55,plain,(
    ! [X41,X42,X43] :
      ( ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ v3_pre_topc(X42,X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | ~ v3_pre_topc(X43,X41)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
      | v3_pre_topc(k3_xboole_0(X42,X43),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).

cnf(c_0_56,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( m1_connsp_2(esk6_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_33]),c_0_43]),c_0_44]),c_0_45])]),c_0_46])).

fof(c_0_61,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | ~ r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X20)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X21)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X21)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),esk4_0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(esk5_0,k1_setfam_1(k2_tarski(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_50]),c_0_43]),c_0_44])]),c_0_46])).

cnf(c_0_63,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_43]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_65,plain,
    ( v3_pre_topc(k3_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X2,X1)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_33]),c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_60]),c_0_43]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),esk4_0)
    | ~ r2_hidden(esk5_0,k1_setfam_1(k2_tarski(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_72,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(X2,X3)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_42]),c_0_43]),c_0_44]),c_0_64]),c_0_45])]),c_0_46]),c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_33]),c_0_43]),c_0_44]),c_0_68]),c_0_45])]),c_0_46]),c_0_67])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_tarski(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_22])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_57])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_setfam_1(k2_tarski(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74]),c_0_43]),c_0_44]),c_0_64]),c_0_68])])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_42]),c_0_43]),c_0_44]),c_0_64]),c_0_45])]),c_0_46]),c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_33]),c_0_43]),c_0_44]),c_0_68]),c_0_45])]),c_0_46]),c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:23:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.41  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.14/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.41  #
% 0.14/0.41  # Preprocessing time       : 0.029 s
% 0.14/0.41  
% 0.14/0.41  # Proof found!
% 0.14/0.41  # SZS status Theorem
% 0.14/0.41  # SZS output start CNFRefutation
% 0.14/0.41  fof(t22_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_waybel_9)).
% 0.14/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.14/0.41  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 0.14/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.14/0.41  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.14/0.41  fof(t21_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_connsp_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_waybel_9)).
% 0.14/0.41  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.14/0.41  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.14/0.41  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.14/0.41  fof(fc6_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k3_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_tops_1)).
% 0.14/0.41  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.14/0.41  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t22_waybel_9])).
% 0.14/0.41  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))&(m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))&~m1_subset_1(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.14/0.41  fof(c_0_17, plain, ![X34, X35]:k1_setfam_1(k2_tarski(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.41  fof(c_0_18, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.14/0.41  fof(c_0_19, plain, ![X47, X48, X49]:(((r2_hidden(X48,X49)|~r2_hidden(X49,u1_struct_0(k9_yellow_6(X47,X48)))|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))|~m1_subset_1(X48,u1_struct_0(X47))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))&(v3_pre_topc(X49,X47)|~r2_hidden(X49,u1_struct_0(k9_yellow_6(X47,X48)))|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))|~m1_subset_1(X48,u1_struct_0(X47))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))))&(~r2_hidden(X48,X49)|~v3_pre_topc(X49,X47)|r2_hidden(X49,u1_struct_0(k9_yellow_6(X47,X48)))|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))|~m1_subset_1(X48,u1_struct_0(X47))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 0.14/0.41  fof(c_0_20, plain, ![X38, X39, X40]:(~r2_hidden(X38,X39)|~m1_subset_1(X39,k1_zfmisc_1(X40))|m1_subset_1(X38,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.41  cnf(c_0_21, negated_conjecture, (~m1_subset_1(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.41  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.41  fof(c_0_24, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.41  fof(c_0_25, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.41  fof(c_0_26, plain, ![X36, X37]:(~r2_hidden(X36,X37)|m1_subset_1(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.14/0.41  cnf(c_0_27, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.41  cnf(c_0_28, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.41  fof(c_0_29, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X31))|k9_subset_1(X31,X32,X33)=k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.14/0.41  fof(c_0_30, plain, ![X50, X51, X52]:(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)|(~m1_subset_1(X51,u1_struct_0(X50))|(~m1_subset_1(X52,u1_struct_0(k9_yellow_6(X50,X51)))|m1_connsp_2(X52,X50,X51)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_waybel_9])])])])).
% 0.14/0.41  cnf(c_0_31, negated_conjecture, (~m1_subset_1(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.41  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 0.14/0.41  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.41  cnf(c_0_34, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.41  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.41  cnf(c_0_36, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.41  cnf(c_0_37, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.41  fof(c_0_38, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(X28))|m1_subset_1(k9_subset_1(X28,X29,X30),k1_zfmisc_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.14/0.41  cnf(c_0_39, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.41  fof(c_0_40, plain, ![X44, X45, X46]:(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|~m1_subset_1(X45,u1_struct_0(X44))|(~m1_connsp_2(X46,X44,X45)|m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.14/0.41  cnf(c_0_41, plain, (v2_struct_0(X1)|m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.41  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.41  cnf(c_0_43, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.41  cnf(c_0_44, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.41  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.41  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.41  fof(c_0_47, plain, ![X26, X27]:(((~m1_subset_1(X27,X26)|r2_hidden(X27,X26)|v1_xboole_0(X26))&(~r2_hidden(X27,X26)|m1_subset_1(X27,X26)|v1_xboole_0(X26)))&((~m1_subset_1(X27,X26)|v1_xboole_0(X27)|~v1_xboole_0(X26))&(~v1_xboole_0(X27)|m1_subset_1(X27,X26)|~v1_xboole_0(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.14/0.41  cnf(c_0_48, negated_conjecture, (~r1_tarski(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.14/0.41  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.41  cnf(c_0_50, plain, (v2_struct_0(X1)|m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.41  cnf(c_0_51, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.41  cnf(c_0_52, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_39, c_0_22])).
% 0.14/0.41  cnf(c_0_53, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.41  cnf(c_0_54, negated_conjecture, (m1_connsp_2(esk7_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45])]), c_0_46])).
% 0.14/0.41  fof(c_0_55, plain, ![X41, X42, X43]:(~v2_pre_topc(X41)|~l1_pre_topc(X41)|~v3_pre_topc(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~v3_pre_topc(X43,X41)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|v3_pre_topc(k3_xboole_0(X42,X43),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).
% 0.14/0.41  cnf(c_0_56, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.41  cnf(c_0_57, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.41  cnf(c_0_58, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.41  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.14/0.41  cnf(c_0_60, negated_conjecture, (m1_connsp_2(esk6_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_33]), c_0_43]), c_0_44]), c_0_45])]), c_0_46])).
% 0.14/0.41  fof(c_0_61, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k3_xboole_0(X15,X16))&(r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k3_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|~r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k3_xboole_0(X15,X16)))&((~r2_hidden(esk3_3(X20,X21,X22),X22)|(~r2_hidden(esk3_3(X20,X21,X22),X20)|~r2_hidden(esk3_3(X20,X21,X22),X21))|X22=k3_xboole_0(X20,X21))&((r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k3_xboole_0(X20,X21))&(r2_hidden(esk3_3(X20,X21,X22),X21)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k3_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.14/0.41  cnf(c_0_62, negated_conjecture, (~v3_pre_topc(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),esk4_0)|~m1_subset_1(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(esk5_0,k1_setfam_1(k2_tarski(esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_50]), c_0_43]), c_0_44])]), c_0_46])).
% 0.14/0.41  cnf(c_0_63, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.41  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_43]), c_0_44]), c_0_45])]), c_0_46])).
% 0.14/0.41  cnf(c_0_65, plain, (v3_pre_topc(k3_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.14/0.41  cnf(c_0_66, plain, (v2_struct_0(X1)|v3_pre_topc(X2,X1)|v1_xboole_0(u1_struct_0(k9_yellow_6(X1,X3)))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.41  cnf(c_0_67, negated_conjecture, (~v1_xboole_0(u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_33]), c_0_59])).
% 0.14/0.41  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_60]), c_0_43]), c_0_44]), c_0_45])]), c_0_46])).
% 0.14/0.41  cnf(c_0_69, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.14/0.41  cnf(c_0_70, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.41  cnf(c_0_71, negated_conjecture, (~v3_pre_topc(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),esk4_0)|~r2_hidden(esk5_0,k1_setfam_1(k2_tarski(esk6_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.14/0.41  cnf(c_0_72, plain, (v3_pre_topc(k1_setfam_1(k2_tarski(X2,X3)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_65, c_0_22])).
% 0.14/0.41  cnf(c_0_73, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_42]), c_0_43]), c_0_44]), c_0_64]), c_0_45])]), c_0_46]), c_0_67])).
% 0.14/0.41  cnf(c_0_74, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_33]), c_0_43]), c_0_44]), c_0_68]), c_0_45])]), c_0_46]), c_0_67])).
% 0.14/0.41  cnf(c_0_75, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_tarski(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_69, c_0_22])).
% 0.14/0.41  cnf(c_0_76, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|v1_xboole_0(u1_struct_0(k9_yellow_6(X1,X2)))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_70, c_0_57])).
% 0.14/0.41  cnf(c_0_77, negated_conjecture, (~r2_hidden(esk5_0,k1_setfam_1(k2_tarski(esk6_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74]), c_0_43]), c_0_44]), c_0_64]), c_0_68])])).
% 0.14/0.41  cnf(c_0_78, plain, (r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_75])).
% 0.14/0.41  cnf(c_0_79, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_42]), c_0_43]), c_0_44]), c_0_64]), c_0_45])]), c_0_46]), c_0_67])).
% 0.14/0.41  cnf(c_0_80, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_33]), c_0_43]), c_0_44]), c_0_68]), c_0_45])]), c_0_46]), c_0_67])).
% 0.14/0.41  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_80])]), ['proof']).
% 0.14/0.41  # SZS output end CNFRefutation
% 0.14/0.41  # Proof object total steps             : 82
% 0.14/0.41  # Proof object clause steps            : 51
% 0.14/0.41  # Proof object formula steps           : 31
% 0.14/0.41  # Proof object conjectures             : 26
% 0.14/0.41  # Proof object clause conjectures      : 23
% 0.14/0.41  # Proof object formula conjectures     : 3
% 0.14/0.41  # Proof object initial clauses used    : 24
% 0.14/0.41  # Proof object initial formulas used   : 15
% 0.14/0.41  # Proof object generating inferences   : 20
% 0.14/0.41  # Proof object simplifying inferences  : 74
% 0.14/0.41  # Training examples: 0 positive, 0 negative
% 0.14/0.41  # Parsed axioms                        : 15
% 0.14/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.41  # Initial clauses                      : 34
% 0.14/0.41  # Removed in clause preprocessing      : 1
% 0.14/0.41  # Initial clauses in saturation        : 33
% 0.14/0.41  # Processed clauses                    : 364
% 0.14/0.41  # ...of these trivial                  : 0
% 0.14/0.41  # ...subsumed                          : 170
% 0.14/0.41  # ...remaining for further processing  : 194
% 0.14/0.41  # Other redundant clauses eliminated   : 3
% 0.14/0.41  # Clauses deleted for lack of memory   : 0
% 0.14/0.41  # Backward-subsumed                    : 7
% 0.14/0.41  # Backward-rewritten                   : 0
% 0.14/0.41  # Generated clauses                    : 873
% 0.14/0.41  # ...of the previous two non-trivial   : 782
% 0.14/0.41  # Contextual simplify-reflections      : 3
% 0.14/0.41  # Paramodulations                      : 866
% 0.14/0.41  # Factorizations                       : 4
% 0.14/0.41  # Equation resolutions                 : 3
% 0.14/0.41  # Propositional unsat checks           : 0
% 0.14/0.41  #    Propositional check models        : 0
% 0.14/0.41  #    Propositional check unsatisfiable : 0
% 0.14/0.41  #    Propositional clauses             : 0
% 0.14/0.41  #    Propositional clauses after purity: 0
% 0.14/0.41  #    Propositional unsat core size     : 0
% 0.14/0.41  #    Propositional preprocessing time  : 0.000
% 0.14/0.41  #    Propositional encoding time       : 0.000
% 0.14/0.41  #    Propositional solver time         : 0.000
% 0.14/0.41  #    Success case prop preproc time    : 0.000
% 0.14/0.41  #    Success case prop encoding time   : 0.000
% 0.14/0.41  #    Success case prop solver time     : 0.000
% 0.14/0.41  # Current number of processed clauses  : 184
% 0.14/0.41  #    Positive orientable unit clauses  : 16
% 0.14/0.41  #    Positive unorientable unit clauses: 0
% 0.14/0.41  #    Negative unit clauses             : 7
% 0.14/0.41  #    Non-unit-clauses                  : 161
% 0.14/0.41  # Current number of unprocessed clauses: 439
% 0.14/0.41  # ...number of literals in the above   : 2143
% 0.14/0.41  # Current number of archived formulas  : 0
% 0.14/0.41  # Current number of archived clauses   : 8
% 0.14/0.41  # Clause-clause subsumption calls (NU) : 4408
% 0.14/0.41  # Rec. Clause-clause subsumption calls : 1858
% 0.14/0.41  # Non-unit clause-clause subsumptions  : 156
% 0.14/0.41  # Unit Clause-clause subsumption calls : 197
% 0.14/0.41  # Rewrite failures with RHS unbound    : 0
% 0.14/0.41  # BW rewrite match attempts            : 3
% 0.14/0.41  # BW rewrite match successes           : 0
% 0.14/0.41  # Condensation attempts                : 0
% 0.14/0.41  # Condensation successes               : 0
% 0.14/0.41  # Termbank termtop insertions          : 18237
% 0.14/0.41  
% 0.14/0.41  # -------------------------------------------------
% 0.14/0.41  # User time                : 0.055 s
% 0.14/0.41  # System time              : 0.008 s
% 0.14/0.41  # Total time               : 0.062 s
% 0.14/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
