%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 664 expanded)
%              Number of clauses        :   49 ( 223 expanded)
%              Number of leaves         :   11 ( 164 expanded)
%              Depth                    :   12
%              Number of atoms          :  337 (4503 expanded)
%              Number of equality atoms :   26 ( 423 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   36 (   2 average)
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
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

fof(c_0_13,plain,(
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

fof(c_0_14,plain,(
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

fof(c_0_15,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_16,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_17,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v3_yellow_6(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v1_yellow_6(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_yellow_6(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v7_waybel_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
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

fof(c_0_29,plain,(
    ! [X17,X18] :
      ( ( ~ r1_tarski(k1_tarski(X17),X18)
        | r2_hidden(X17,X18) )
      & ( ~ r2_hidden(X17,X18)
        | r1_tarski(k1_tarski(X17),X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_32,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( v3_yellow_6(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v8_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_35,plain,(
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

fof(c_0_36,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X19)
      | v1_xboole_0(X20)
      | ~ v1_zfmisc_1(X20)
      | ~ r1_tarski(X19,X20)
      | X19 = X20 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k11_yellow_6(esk3_0,esk4_0),k10_yellow_6(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_zfmisc_1(k10_yellow_6(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk3_0,esk4_0),k10_yellow_6(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_27]),c_0_26])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_tarski(k11_yellow_6(esk3_0,esk4_0)),k10_yellow_6(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_zfmisc_1(k10_yellow_6(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_23]),c_0_34]),c_0_21]),c_0_22]),c_0_24]),c_0_25])]),c_0_27]),c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(k10_yellow_6(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_tarski(k4_yellow_6(esk3_0,esk4_0)),k10_yellow_6(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( k1_tarski(k11_yellow_6(esk3_0,esk4_0)) = k10_yellow_6(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),c_0_52]),c_0_53])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( k1_tarski(k4_yellow_6(esk3_0,esk4_0)) = k10_yellow_6(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_55]),c_0_51])]),c_0_52]),c_0_53])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k11_yellow_6(esk3_0,esk4_0),X1)
    | ~ r1_tarski(k10_yellow_6(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k10_yellow_6(esk3_0,esk4_0),k1_zfmisc_1(k4_yellow_6(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k11_yellow_6(esk3_0,esk4_0),k1_zfmisc_1(k4_yellow_6(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk3_0,esk4_0),X1)
    | ~ r1_tarski(k10_yellow_6(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k10_yellow_6(esk3_0,esk4_0),k1_zfmisc_1(k11_yellow_6(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_66,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k11_yellow_6(esk3_0,esk4_0),k4_yellow_6(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k11_yellow_6(esk3_0,esk4_0) != k4_yellow_6(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk3_0,esk4_0),k1_zfmisc_1(k11_yellow_6(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(k4_yellow_6(esk3_0,esk4_0),k11_yellow_6(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t45_yellow_6, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>k11_yellow_6(X1,X2)=k4_yellow_6(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_6)).
% 0.13/0.38  fof(d20_yellow_6, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k11_yellow_6(X1,X2)<=>r2_hidden(X3,k10_yellow_6(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_yellow_6)).
% 0.13/0.38  fof(dt_k11_yellow_6, axiom, ![X1, X2]:(((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_yellow_6)).
% 0.13/0.38  fof(cc4_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(l1_waybel_0(X2,X1)=>((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))=>(((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_6)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t42_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 0.13/0.38  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.13/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.13/0.38  fof(fc22_yellow_6, axiom, ![X1, X2]:((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>v1_zfmisc_1(k10_yellow_6(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc22_yellow_6)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>k11_yellow_6(X1,X2)=k4_yellow_6(X1,X2)))), inference(assume_negation,[status(cth)],[t45_yellow_6])).
% 0.13/0.38  fof(c_0_12, plain, ![X23, X24, X25]:((X25!=k11_yellow_6(X23,X24)|r2_hidden(X25,k10_yellow_6(X23,X24))|~m1_subset_1(X25,u1_struct_0(X23))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~v3_yellow_6(X24,X23)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~v8_pre_topc(X23)|~l1_pre_topc(X23)))&(~r2_hidden(X25,k10_yellow_6(X23,X24))|X25=k11_yellow_6(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~v3_yellow_6(X24,X23)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~v8_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_yellow_6])])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X26, X27]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~v8_pre_topc(X26)|~l1_pre_topc(X26)|v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~v3_yellow_6(X27,X26)|~l1_waybel_0(X27,X26)|m1_subset_1(k11_yellow_6(X26,X27),u1_struct_0(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k11_yellow_6])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X21, X22]:((((~v2_struct_0(X22)|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~v1_yellow_6(X22,X21))|~l1_waybel_0(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(v4_orders_2(X22)|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~v1_yellow_6(X22,X21))|~l1_waybel_0(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(v7_waybel_0(X22)|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~v1_yellow_6(X22,X21))|~l1_waybel_0(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(v3_yellow_6(X22,X21)|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~v1_yellow_6(X22,X21))|~l1_waybel_0(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_yellow_6])])])])])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v8_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((((~v2_struct_0(esk4_0)&v4_orders_2(esk4_0))&v7_waybel_0(esk4_0))&v1_yellow_6(esk4_0,esk3_0))&l1_waybel_0(esk4_0,esk3_0))&k11_yellow_6(esk3_0,esk4_0)!=k4_yellow_6(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_17, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k11_yellow_6(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~v3_yellow_6(X3,X2)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~v8_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v3_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_19, plain, (v3_yellow_6(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~v1_yellow_6(X1,X2)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v1_yellow_6(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v7_waybel_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (l1_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_28, plain, ![X30, X31]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~v1_yellow_6(X31,X30)|~l1_waybel_0(X31,X30)|r2_hidden(k4_yellow_6(X30,X31),k10_yellow_6(X30,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_6])])])])).
% 0.13/0.38  fof(c_0_29, plain, ![X17, X18]:((~r1_tarski(k1_tarski(X17),X18)|r2_hidden(X17,X18))&(~r2_hidden(X17,X18)|r1_tarski(k1_tarski(X17),X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_31, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|~r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.13/0.38  cnf(c_0_32, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k11_yellow_6(X2,X1),k10_yellow_6(X2,X1))|~v8_pre_topc(X2)|~v3_yellow_6(X1,X2)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v3_yellow_6(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26]), c_0_27])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (v8_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_35, plain, ![X28, X29]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~v8_pre_topc(X28)|~l1_pre_topc(X28)|v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28)|v1_zfmisc_1(k10_yellow_6(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc22_yellow_6])])])).
% 0.13/0.38  fof(c_0_36, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v1_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  fof(c_0_41, plain, ![X19, X20]:(v1_xboole_0(X19)|(v1_xboole_0(X20)|~v1_zfmisc_1(X20)|(~r1_tarski(X19,X20)|X19=X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.13/0.38  cnf(c_0_42, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(k11_yellow_6(esk3_0,esk4_0),k10_yellow_6(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26]), c_0_27])).
% 0.13/0.38  cnf(c_0_44, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v1_zfmisc_1(k10_yellow_6(X1,X2))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_45, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_yellow_6(esk3_0,esk4_0),k10_yellow_6(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_27]), c_0_26])).
% 0.13/0.38  cnf(c_0_47, plain, (r2_hidden(X1,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_48, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_49, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_tarski(k11_yellow_6(esk3_0,esk4_0)),k10_yellow_6(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (v1_zfmisc_1(k10_yellow_6(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_23]), c_0_34]), c_0_21]), c_0_22]), c_0_24]), c_0_25])]), c_0_27]), c_0_26])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(k10_yellow_6(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_53, plain, (~v1_xboole_0(k1_tarski(X1))), inference(spm,[status(thm)],[c_0_45, c_0_47])).
% 0.13/0.38  cnf(c_0_54, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_39])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_tarski(k4_yellow_6(esk3_0,esk4_0)),k10_yellow_6(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_46])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (k1_tarski(k11_yellow_6(esk3_0,esk4_0))=k10_yellow_6(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), c_0_52]), c_0_53])).
% 0.13/0.38  cnf(c_0_57, plain, (r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_54])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (k1_tarski(k4_yellow_6(esk3_0,esk4_0))=k10_yellow_6(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_55]), c_0_51])]), c_0_52]), c_0_53])).
% 0.13/0.38  cnf(c_0_59, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(k11_yellow_6(esk3_0,esk4_0),X1)|~r1_tarski(k10_yellow_6(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_56])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (r1_tarski(k10_yellow_6(esk3_0,esk4_0),k1_zfmisc_1(k4_yellow_6(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.38  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_59])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(k11_yellow_6(esk3_0,esk4_0),k1_zfmisc_1(k4_yellow_6(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(k4_yellow_6(esk3_0,esk4_0),X1)|~r1_tarski(k10_yellow_6(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_58])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (r1_tarski(k10_yellow_6(esk3_0,esk4_0),k1_zfmisc_1(k11_yellow_6(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_57, c_0_56])).
% 0.13/0.38  cnf(c_0_66, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(k11_yellow_6(esk3_0,esk4_0),k4_yellow_6(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (k11_yellow_6(esk3_0,esk4_0)!=k4_yellow_6(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (r2_hidden(k4_yellow_6(esk3_0,esk4_0),k1_zfmisc_1(k11_yellow_6(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (~r1_tarski(k4_yellow_6(esk3_0,esk4_0),k11_yellow_6(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_69]), c_0_70]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 72
% 0.13/0.38  # Proof object clause steps            : 49
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 31
% 0.13/0.38  # Proof object clause conjectures      : 28
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 23
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 22
% 0.13/0.38  # Proof object simplifying inferences  : 48
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 31
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 100
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 7
% 0.13/0.38  # ...remaining for further processing  : 92
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 114
% 0.13/0.38  # ...of the previous two non-trivial   : 91
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 106
% 0.13/0.38  # Factorizations                       : 2
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
% 0.13/0.38  # Current number of processed clauses  : 57
% 0.13/0.38  #    Positive orientable unit clauses  : 25
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 7
% 0.13/0.38  #    Non-unit-clauses                  : 25
% 0.13/0.38  # Current number of unprocessed clauses: 45
% 0.13/0.38  # ...number of literals in the above   : 130
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 30
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 342
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 47
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.38  # Unit Clause-clause subsumption calls : 58
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 7
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4732
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.035 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
