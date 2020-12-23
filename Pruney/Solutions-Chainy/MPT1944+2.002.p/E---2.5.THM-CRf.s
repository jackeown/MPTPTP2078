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
% DateTime   : Thu Dec  3 11:21:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 241 expanded)
%              Number of clauses        :   34 (  81 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  396 (1738 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   81 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_yellow_6,conjecture,(
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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t25_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v1_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => k2_waybel_0(X1,X2,X3) = k4_yellow_6(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_6)).

fof(d11_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ? [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( r1_orders_2(X2,X4,X5)
                       => r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

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

fof(d18_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k10_yellow_6(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_connsp_2(X5,X1,X4)
                         => r1_waybel_0(X1,X2,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

fof(dt_k10_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(dt_k4_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t42_yellow_6])).

fof(c_0_11,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | l1_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & ~ v2_struct_0(esk8_0)
    & v4_orders_2(esk8_0)
    & v7_waybel_0(esk8_0)
    & v1_yellow_6(esk8_0,esk7_0)
    & l1_waybel_0(esk8_0,esk7_0)
    & ~ r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | v2_struct_0(X37)
      | ~ v4_orders_2(X37)
      | ~ v7_waybel_0(X37)
      | ~ v1_yellow_6(X37,X36)
      | ~ l1_waybel_0(X37,X36)
      | ~ m1_subset_1(X38,u1_struct_0(X37))
      | k2_waybel_0(X36,X37,X38) = k4_yellow_6(X36,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow_6])])])])).

cnf(c_0_14,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X19,X20,X21] :
      ( ( m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X16))
        | ~ r1_waybel_0(X15,X16,X17)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r1_orders_2(X16,esk2_3(X15,X16,X17),X19)
        | r2_hidden(k2_waybel_0(X15,X16,X19),X17)
        | ~ r1_waybel_0(X15,X16,X17)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( m1_subset_1(esk3_4(X15,X16,X20,X21),u1_struct_0(X16))
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | r1_waybel_0(X15,X16,X20)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( r1_orders_2(X16,X21,esk3_4(X15,X16,X20,X21))
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | r1_waybel_0(X15,X16,X20)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( ~ r2_hidden(k2_waybel_0(X15,X16,esk3_4(X15,X16,X20,X21)),X20)
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | r1_waybel_0(X15,X16,X20)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k4_yellow_6(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_yellow_6(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v7_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_25,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ m1_connsp_2(X13,X12,X14)
      | r2_hidden(X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

fof(c_0_26,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_connsp_2(X11,X9,X10)
      | m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_27,plain,(
    ! [X23,X24,X25,X26,X27,X31] :
      ( ( ~ r2_hidden(X26,X25)
        | ~ m1_connsp_2(X27,X23,X26)
        | r1_waybel_0(X23,X24,X27)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | X25 != k10_yellow_6(X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_connsp_2(esk4_4(X23,X24,X25,X26),X23,X26)
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | X25 != k10_yellow_6(X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ r1_waybel_0(X23,X24,esk4_4(X23,X24,X25,X26))
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | X25 != k10_yellow_6(X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk5_3(X23,X24,X25),u1_struct_0(X23))
        | X25 = k10_yellow_6(X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_connsp_2(esk6_3(X23,X24,X25),X23,esk5_3(X23,X24,X25))
        | ~ r2_hidden(esk5_3(X23,X24,X25),X25)
        | X25 = k10_yellow_6(X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ r1_waybel_0(X23,X24,esk6_3(X23,X24,X25))
        | ~ r2_hidden(esk5_3(X23,X24,X25),X25)
        | X25 = k10_yellow_6(X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk5_3(X23,X24,X25),X25)
        | ~ m1_connsp_2(X31,X23,esk5_3(X23,X24,X25))
        | r1_waybel_0(X23,X24,X31)
        | X25 = k10_yellow_6(X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_28,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ v4_orders_2(X33)
      | ~ v7_waybel_0(X33)
      | ~ l1_waybel_0(X33,X32)
      | m1_subset_1(k10_yellow_6(X32,X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_29,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( k2_waybel_0(esk7_0,esk8_0,X1) = k4_yellow_6(esk7_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( m1_connsp_2(esk4_4(X1,X2,X3,X4),X1,X4)
    | r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ l1_struct_0(X34)
      | ~ l1_waybel_0(X35,X34)
      | m1_subset_1(k4_yellow_6(X34,X35),u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,X1)
    | ~ r2_hidden(k4_yellow_6(esk7_0,esk8_0),X1)
    | ~ m1_subset_1(esk3_4(esk7_0,esk8_0,X1,X2),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_21]),c_0_24])]),c_0_22]),c_0_23])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ m1_connsp_2(X2,X3,X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | m1_connsp_2(esk4_4(X2,X3,k10_yellow_6(X2,X3),X1),X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,X1)
    | ~ r2_hidden(k4_yellow_6(esk7_0,esk8_0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_21]),c_0_24])]),c_0_22]),c_0_23])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,esk4_4(X2,X3,k10_yellow_6(X2,X3),X1))
    | r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_43,plain,(
    ! [X6] : m1_subset_1(esk1_1(X6),X6) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk7_0,esk8_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_21]),c_0_24])]),c_0_23])).

cnf(c_0_45,plain,
    ( r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,esk4_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk7_0,esk8_0)))
    | r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_30])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ r1_waybel_0(X2,X3,esk4_4(X2,X3,k10_yellow_6(X2,X3),X1))
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,esk4_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk7_0,esk8_0)))
    | r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_19]),c_0_20]),c_0_21]),c_0_51]),c_0_15]),c_0_52])]),c_0_53]),c_0_23]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t42_yellow_6, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(t25_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>k2_waybel_0(X1,X2,X3)=k4_yellow_6(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_6)).
% 0.13/0.38  fof(d11_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r2_hidden(k2_waybel_0(X1,X2,X5),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 0.13/0.38  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.13/0.38  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.13/0.38  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.13/0.38  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.13/0.38  fof(dt_k4_yellow_6, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_struct_0(X1))&l1_waybel_0(X2,X1))=>m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 0.13/0.38  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))))), inference(assume_negation,[status(cth)],[t42_yellow_6])).
% 0.13/0.38  fof(c_0_11, plain, ![X8]:(~l1_pre_topc(X8)|l1_struct_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk7_0)&v2_pre_topc(esk7_0))&l1_pre_topc(esk7_0))&(((((~v2_struct_0(esk8_0)&v4_orders_2(esk8_0))&v7_waybel_0(esk8_0))&v1_yellow_6(esk8_0,esk7_0))&l1_waybel_0(esk8_0,esk7_0))&~r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~l1_struct_0(X36)|(v2_struct_0(X37)|~v4_orders_2(X37)|~v7_waybel_0(X37)|~v1_yellow_6(X37,X36)|~l1_waybel_0(X37,X36)|(~m1_subset_1(X38,u1_struct_0(X37))|k2_waybel_0(X36,X37,X38)=k4_yellow_6(X36,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow_6])])])])).
% 0.13/0.38  cnf(c_0_14, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_16, plain, ![X15, X16, X17, X19, X20, X21]:(((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X16))|~r1_waybel_0(X15,X16,X17)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&(~m1_subset_1(X19,u1_struct_0(X16))|(~r1_orders_2(X16,esk2_3(X15,X16,X17),X19)|r2_hidden(k2_waybel_0(X15,X16,X19),X17))|~r1_waybel_0(X15,X16,X17)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15))))&((m1_subset_1(esk3_4(X15,X16,X20,X21),u1_struct_0(X16))|~m1_subset_1(X21,u1_struct_0(X16))|r1_waybel_0(X15,X16,X20)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&((r1_orders_2(X16,X21,esk3_4(X15,X16,X20,X21))|~m1_subset_1(X21,u1_struct_0(X16))|r1_waybel_0(X15,X16,X20)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&(~r2_hidden(k2_waybel_0(X15,X16,esk3_4(X15,X16,X20,X21)),X20)|~m1_subset_1(X21,u1_struct_0(X16))|r1_waybel_0(X15,X16,X20)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).
% 0.13/0.38  cnf(c_0_17, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_waybel_0(X1,X2,X3)=k4_yellow_6(X1,X2)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v1_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (v1_yellow_6(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v7_waybel_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v4_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  fof(c_0_25, plain, ![X12, X13, X14]:(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(~m1_subset_1(X14,u1_struct_0(X12))|(~m1_connsp_2(X13,X12,X14)|r2_hidden(X14,X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.13/0.38  fof(c_0_26, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)|~m1_subset_1(X10,u1_struct_0(X9))|(~m1_connsp_2(X11,X9,X10)|m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.13/0.38  fof(c_0_27, plain, ![X23, X24, X25, X26, X27, X31]:(((~r2_hidden(X26,X25)|(~m1_connsp_2(X27,X23,X26)|r1_waybel_0(X23,X24,X27))|~m1_subset_1(X26,u1_struct_0(X23))|X25!=k10_yellow_6(X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&((m1_connsp_2(esk4_4(X23,X24,X25,X26),X23,X26)|r2_hidden(X26,X25)|~m1_subset_1(X26,u1_struct_0(X23))|X25!=k10_yellow_6(X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~r1_waybel_0(X23,X24,esk4_4(X23,X24,X25,X26))|r2_hidden(X26,X25)|~m1_subset_1(X26,u1_struct_0(X23))|X25!=k10_yellow_6(X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))))&((m1_subset_1(esk5_3(X23,X24,X25),u1_struct_0(X23))|X25=k10_yellow_6(X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(((m1_connsp_2(esk6_3(X23,X24,X25),X23,esk5_3(X23,X24,X25))|~r2_hidden(esk5_3(X23,X24,X25),X25)|X25=k10_yellow_6(X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~r1_waybel_0(X23,X24,esk6_3(X23,X24,X25))|~r2_hidden(esk5_3(X23,X24,X25),X25)|X25=k10_yellow_6(X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23))))&(r2_hidden(esk5_3(X23,X24,X25),X25)|(~m1_connsp_2(X31,X23,esk5_3(X23,X24,X25))|r1_waybel_0(X23,X24,X31))|X25=k10_yellow_6(X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.13/0.38  fof(c_0_28, plain, ![X32, X33]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32)|m1_subset_1(k10_yellow_6(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.13/0.38  cnf(c_0_29, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k2_waybel_0(esk7_0,esk8_0,X1)=k4_yellow_6(esk7_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22]), c_0_23]), c_0_24])])).
% 0.13/0.38  cnf(c_0_31, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_32, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_33, plain, (m1_connsp_2(esk4_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  fof(c_0_35, plain, ![X34, X35]:(v2_struct_0(X34)|~l1_struct_0(X34)|~l1_waybel_0(X35,X34)|m1_subset_1(k4_yellow_6(X34,X35),u1_struct_0(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,X1)|~r2_hidden(k4_yellow_6(esk7_0,esk8_0),X1)|~m1_subset_1(esk3_4(esk7_0,esk8_0,X1,X2),u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_21]), c_0_24])]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_37, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_38, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~m1_connsp_2(X2,X3,X1)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_39, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|m1_connsp_2(esk4_4(X2,X3,k10_yellow_6(X2,X3),X1),X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_34])).
% 0.13/0.38  cnf(c_0_40, plain, (v2_struct_0(X1)|m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,X1)|~r2_hidden(k4_yellow_6(esk7_0,esk8_0),X1)|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_21]), c_0_24])]), c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_42, plain, (r2_hidden(X1,esk4_4(X2,X3,k10_yellow_6(X2,X3),X1))|r2_hidden(X1,k10_yellow_6(X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  fof(c_0_43, plain, ![X6]:m1_subset_1(esk1_1(X6),X6), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(k2_waybel_0(esk7_0,esk8_0,X1),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_21]), c_0_24])]), c_0_23])).
% 0.13/0.38  cnf(c_0_45, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,esk4_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk7_0,esk8_0)))|r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_47, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_44, c_0_30])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~r1_waybel_0(X2,X3,esk4_4(X2,X3,k10_yellow_6(X2,X3),X1))|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_34])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,esk4_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk7_0,esk8_0)))|r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (~r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_19]), c_0_20]), c_0_21]), c_0_51]), c_0_15]), c_0_52])]), c_0_53]), c_0_23]), c_0_22]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 55
% 0.13/0.38  # Proof object clause steps            : 34
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 22
% 0.13/0.38  # Proof object clause conjectures      : 19
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 20
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 11
% 0.13/0.38  # Proof object simplifying inferences  : 37
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 28
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 101
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 17
% 0.13/0.38  # ...remaining for further processing  : 84
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 6
% 0.13/0.38  # Backward-rewritten                   : 1
% 0.13/0.38  # Generated clauses                    : 65
% 0.13/0.38  # ...of the previous two non-trivial   : 59
% 0.13/0.38  # Contextual simplify-reflections      : 8
% 0.13/0.38  # Paramodulations                      : 62
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
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
% 0.13/0.38  # Current number of processed clauses  : 46
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 34
% 0.13/0.38  # Current number of unprocessed clauses: 10
% 0.13/0.38  # ...number of literals in the above   : 129
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 35
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1264
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 75
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 30
% 0.13/0.38  # Unit Clause-clause subsumption calls : 20
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6403
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.038 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.042 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
