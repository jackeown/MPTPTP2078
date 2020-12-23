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
% DateTime   : Thu Dec  3 11:21:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 221 expanded)
%              Number of clauses        :   35 (  70 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  312 (1577 expanded)
%              Number of equality atoms :   31 ( 157 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v1_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => k11_yellow_6(X1,X2) = k4_yellow_6(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t42_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v1_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(fc22_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => v1_zfmisc_1(k10_yellow_6(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_yellow_6)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(d20_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v3_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X3 = k11_yellow_6(X1,X2)
              <=> r2_hidden(X3,k10_yellow_6(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).

fof(dt_k11_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & v3_yellow_6(X2,X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).

fof(cc4_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & v1_yellow_6(X2,X1) )
           => ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & v3_yellow_6(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v8_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & v1_yellow_6(X2,X1)
              & l1_waybel_0(X2,X1) )
           => k11_yellow_6(X1,X2) = k4_yellow_6(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t45_yellow_6])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( ( ~ r1_tarski(k1_tarski(X17),X18)
        | r2_hidden(X17,X18) )
      & ( ~ r2_hidden(X17,X18)
        | r1_tarski(k1_tarski(X17),X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_14,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v4_orders_2(X31)
      | ~ v7_waybel_0(X31)
      | ~ v1_yellow_6(X31,X30)
      | ~ l1_waybel_0(X31,X30)
      | r2_hidden(k4_yellow_6(X30,X31),k10_yellow_6(X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_6])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v8_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v4_orders_2(esk4_0)
    & v7_waybel_0(esk4_0)
    & v1_yellow_6(esk4_0,esk3_0)
    & l1_waybel_0(esk4_0,esk3_0)
    & k11_yellow_6(esk3_0,esk4_0) != k4_yellow_6(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_17,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | esk2_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | esk2_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_yellow_6(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v7_waybel_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_29,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ v8_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ v4_orders_2(X29)
      | ~ v7_waybel_0(X29)
      | ~ l1_waybel_0(X29,X28)
      | v1_zfmisc_1(k10_yellow_6(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc22_yellow_6])])])).

fof(c_0_30,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X16] : ~ v1_xboole_0(k1_tarski(X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_32,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_33,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X19)
      | v1_xboole_0(X20)
      | ~ v1_zfmisc_1(X20)
      | ~ r1_tarski(X19,X20)
      | X19 = X20 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk3_0,esk4_0),k10_yellow_6(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_zfmisc_1(k10_yellow_6(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v8_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_40,plain,(
    ! [X23,X24,X25] :
      ( ( X25 != k11_yellow_6(X23,X24)
        | r2_hidden(X25,k10_yellow_6(X23,X24))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ v3_yellow_6(X24,X23)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ v8_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ r2_hidden(X25,k10_yellow_6(X23,X24))
        | X25 = k11_yellow_6(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ v3_yellow_6(X24,X23)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ v8_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_yellow_6])])])])])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ v8_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ v4_orders_2(X27)
      | ~ v7_waybel_0(X27)
      | ~ v3_yellow_6(X27,X26)
      | ~ l1_waybel_0(X27,X26)
      | m1_subset_1(k11_yellow_6(X26,X27),u1_struct_0(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k11_yellow_6])])])).

fof(c_0_42,plain,(
    ! [X21,X22] :
      ( ( ~ v2_struct_0(X22)
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ v1_yellow_6(X22,X21)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v4_orders_2(X22)
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ v1_yellow_6(X22,X21)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ v1_yellow_6(X22,X21)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v3_yellow_6(X22,X21)
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ v1_yellow_6(X22,X21)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_yellow_6])])])])])).

cnf(c_0_43,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_tarski(k4_yellow_6(esk3_0,esk4_0),k4_yellow_6(esk3_0,esk4_0)),k10_yellow_6(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( v1_zfmisc_1(k10_yellow_6(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_37]),c_0_22]),c_0_23]),c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(k10_yellow_6(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k11_yellow_6(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ v3_yellow_6(X3,X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ v8_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v3_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( v3_yellow_6(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v1_yellow_6(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k2_tarski(k4_yellow_6(esk3_0,esk4_0),k4_yellow_6(esk3_0,esk4_0)) = k10_yellow_6(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),c_0_47]),c_0_48])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(k11_yellow_6(X2,X1),k10_yellow_6(X2,X1))
    | ~ v8_pre_topc(X2)
    | ~ v3_yellow_6(X1,X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_28]),c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k4_yellow_6(esk3_0,esk4_0)
    | ~ r2_hidden(X1,k10_yellow_6(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k11_yellow_6(esk3_0,esk4_0),k10_yellow_6(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_37]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_28]),c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( k11_yellow_6(esk3_0,esk4_0) != k4_yellow_6(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t45_yellow_6, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>k11_yellow_6(X1,X2)=k4_yellow_6(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_6)).
% 0.13/0.38  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t42_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(fc22_yellow_6, axiom, ![X1, X2]:((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>v1_zfmisc_1(k10_yellow_6(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc22_yellow_6)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.13/0.38  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.13/0.38  fof(d20_yellow_6, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k11_yellow_6(X1,X2)<=>r2_hidden(X3,k10_yellow_6(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_yellow_6)).
% 0.13/0.38  fof(dt_k11_yellow_6, axiom, ![X1, X2]:(((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_yellow_6)).
% 0.13/0.38  fof(cc4_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(l1_waybel_0(X2,X1)=>((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))=>(((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_6)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>k11_yellow_6(X1,X2)=k4_yellow_6(X1,X2)))), inference(assume_negation,[status(cth)],[t45_yellow_6])).
% 0.13/0.38  fof(c_0_13, plain, ![X17, X18]:((~r1_tarski(k1_tarski(X17),X18)|r2_hidden(X17,X18))&(~r2_hidden(X17,X18)|r1_tarski(k1_tarski(X17),X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.13/0.38  fof(c_0_14, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_15, plain, ![X30, X31]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~v1_yellow_6(X31,X30)|~l1_waybel_0(X31,X30)|r2_hidden(k4_yellow_6(X30,X31),k10_yellow_6(X30,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_6])])])])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v8_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((((~v2_struct_0(esk4_0)&v4_orders_2(esk4_0))&v7_waybel_0(esk4_0))&v1_yellow_6(esk4_0,esk3_0))&l1_waybel_0(esk4_0,esk3_0))&k11_yellow_6(esk3_0,esk4_0)!=k4_yellow_6(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|X10=X8|X9!=k1_tarski(X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_tarski(X8)))&((~r2_hidden(esk2_2(X12,X13),X13)|esk2_2(X12,X13)!=X12|X13=k1_tarski(X12))&(r2_hidden(esk2_2(X12,X13),X13)|esk2_2(X12,X13)=X12|X13=k1_tarski(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_18, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_20, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v1_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v1_yellow_6(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (v7_waybel_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (l1_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_29, plain, ![X28, X29]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~v8_pre_topc(X28)|~l1_pre_topc(X28)|v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28)|v1_zfmisc_1(k10_yellow_6(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc22_yellow_6])])])).
% 0.13/0.38  fof(c_0_30, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  fof(c_0_31, plain, ![X16]:~v1_xboole_0(k1_tarski(X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.13/0.38  cnf(c_0_32, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_33, plain, ![X19, X20]:(v1_xboole_0(X19)|(v1_xboole_0(X20)|~v1_zfmisc_1(X20)|(~r1_tarski(X19,X20)|X19=X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.13/0.38  cnf(c_0_34, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_yellow_6(esk3_0,esk4_0),k10_yellow_6(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_28])).
% 0.13/0.38  cnf(c_0_36, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v1_zfmisc_1(k10_yellow_6(X1,X2))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (v8_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_38, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_39, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  fof(c_0_40, plain, ![X23, X24, X25]:((X25!=k11_yellow_6(X23,X24)|r2_hidden(X25,k10_yellow_6(X23,X24))|~m1_subset_1(X25,u1_struct_0(X23))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~v3_yellow_6(X24,X23)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~v8_pre_topc(X23)|~l1_pre_topc(X23)))&(~r2_hidden(X25,k10_yellow_6(X23,X24))|X25=k11_yellow_6(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~v3_yellow_6(X24,X23)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~v8_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_yellow_6])])])])])).
% 0.13/0.38  fof(c_0_41, plain, ![X26, X27]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~v8_pre_topc(X26)|~l1_pre_topc(X26)|v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~v3_yellow_6(X27,X26)|~l1_waybel_0(X27,X26)|m1_subset_1(k11_yellow_6(X26,X27),u1_struct_0(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k11_yellow_6])])])).
% 0.13/0.38  fof(c_0_42, plain, ![X21, X22]:((((~v2_struct_0(X22)|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~v1_yellow_6(X22,X21))|~l1_waybel_0(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(v4_orders_2(X22)|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~v1_yellow_6(X22,X21))|~l1_waybel_0(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(v7_waybel_0(X22)|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~v1_yellow_6(X22,X21))|~l1_waybel_0(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(v3_yellow_6(X22,X21)|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~v1_yellow_6(X22,X21))|~l1_waybel_0(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_yellow_6])])])])])).
% 0.13/0.38  cnf(c_0_43, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_19])).
% 0.13/0.38  cnf(c_0_44, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_tarski(k4_yellow_6(esk3_0,esk4_0),k4_yellow_6(esk3_0,esk4_0)),k10_yellow_6(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (v1_zfmisc_1(k10_yellow_6(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_24]), c_0_37]), c_0_22]), c_0_23]), c_0_25]), c_0_26])]), c_0_27]), c_0_28])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(k10_yellow_6(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_35])).
% 0.13/0.38  cnf(c_0_48, plain, (~v1_xboole_0(k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_39, c_0_19])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k11_yellow_6(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~v3_yellow_6(X3,X2)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~v8_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v3_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_51, plain, (v3_yellow_6(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~v1_yellow_6(X1,X2)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_52, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k2_tarski(k4_yellow_6(esk3_0,esk4_0),k4_yellow_6(esk3_0,esk4_0))=k10_yellow_6(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])]), c_0_47]), c_0_48])).
% 0.13/0.38  cnf(c_0_54, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k11_yellow_6(X2,X1),k10_yellow_6(X2,X1))|~v8_pre_topc(X2)|~v3_yellow_6(X1,X2)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]), c_0_50])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (v3_yellow_6(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_28]), c_0_27])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (X1=k4_yellow_6(esk3_0,esk4_0)|~r2_hidden(X1,k10_yellow_6(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (r2_hidden(k11_yellow_6(esk3_0,esk4_0),k10_yellow_6(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_37]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_28]), c_0_27])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (k11_yellow_6(esk3_0,esk4_0)!=k4_yellow_6(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 60
% 0.13/0.38  # Proof object clause steps            : 35
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 22
% 0.13/0.38  # Proof object clause conjectures      : 19
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 21
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 9
% 0.13/0.38  # Proof object simplifying inferences  : 44
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 30
% 0.13/0.38  # Removed in clause preprocessing      : 4
% 0.13/0.38  # Initial clauses in saturation        : 26
% 0.13/0.38  # Processed clauses                    : 71
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 4
% 0.13/0.38  # ...remaining for further processing  : 67
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 1
% 0.13/0.38  # Generated clauses                    : 54
% 0.13/0.38  # ...of the previous two non-trivial   : 47
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 50
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 5
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 37
% 0.13/0.38  #    Positive orientable unit clauses  : 16
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 5
% 0.13/0.38  #    Non-unit-clauses                  : 16
% 0.13/0.38  # Current number of unprocessed clauses: 27
% 0.13/0.38  # ...number of literals in the above   : 100
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 28
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 315
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 17
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.38  # Unit Clause-clause subsumption calls : 7
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3762
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.031 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
