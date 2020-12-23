%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:19 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 287 expanded)
%              Number of clauses        :   39 (  96 expanded)
%              Number of leaves         :   10 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  441 (2062 expanded)
%              Number of equality atoms :   17 (  40 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(dt_k2_waybel_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

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
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ l1_struct_0(X37)
      | v2_struct_0(X38)
      | ~ v4_orders_2(X38)
      | ~ v7_waybel_0(X38)
      | ~ v1_yellow_6(X38,X37)
      | ~ l1_waybel_0(X38,X37)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | k2_waybel_0(X37,X38,X39) = k4_yellow_6(X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow_6])])])])).

fof(c_0_12,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | l1_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_13,negated_conjecture,
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

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k4_yellow_6(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_waybel_0(X1,X2,X3) = k2_waybel_0(X1,X2,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_yellow_6(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v7_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
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

cnf(c_0_26,negated_conjecture,
    ( k2_waybel_0(esk7_0,esk8_0,X1) = k2_waybel_0(esk7_0,esk8_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

fof(c_0_27,plain,(
    ! [X6] : m1_subset_1(esk1_1(X6),X6) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_28,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k2_waybel_0(esk7_0,esk8_0,X1) = k4_yellow_6(esk7_0,esk8_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_26]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_24]),c_0_23])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ m1_connsp_2(X13,X12,X14)
      | r2_hidden(X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

fof(c_0_33,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_connsp_2(X11,X9,X10)
      | m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_34,plain,(
    ! [X26,X27,X28,X29,X30,X34] :
      ( ( ~ r2_hidden(X29,X28)
        | ~ m1_connsp_2(X30,X26,X29)
        | r1_waybel_0(X26,X27,X30)
        | ~ m1_subset_1(X29,u1_struct_0(X26))
        | X28 != k10_yellow_6(X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_connsp_2(esk4_4(X26,X27,X28,X29),X26,X29)
        | r2_hidden(X29,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X26))
        | X28 != k10_yellow_6(X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_waybel_0(X26,X27,esk4_4(X26,X27,X28,X29))
        | r2_hidden(X29,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X26))
        | X28 != k10_yellow_6(X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk5_3(X26,X27,X28),u1_struct_0(X26))
        | X28 = k10_yellow_6(X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_connsp_2(esk6_3(X26,X27,X28),X26,esk5_3(X26,X27,X28))
        | ~ r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k10_yellow_6(X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_waybel_0(X26,X27,esk6_3(X26,X27,X28))
        | ~ r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k10_yellow_6(X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(esk5_3(X26,X27,X28),X28)
        | ~ m1_connsp_2(X34,X26,esk5_3(X26,X27,X28))
        | r1_waybel_0(X26,X27,X34)
        | X28 = k10_yellow_6(X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_35,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ v4_orders_2(X36)
      | ~ v7_waybel_0(X36)
      | ~ l1_waybel_0(X36,X35)
      | m1_subset_1(k10_yellow_6(X35,X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_36,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r2_hidden(k4_yellow_6(X1,X2),X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k2_waybel_0(esk7_0,esk8_0,X1) = k4_yellow_6(esk7_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,X1)
    | ~ r2_hidden(k2_waybel_0(esk7_0,esk8_0,X2),X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ m1_connsp_2(X2,X3,X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41])).

fof(c_0_45,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ l1_struct_0(X23)
      | v2_struct_0(X24)
      | ~ l1_waybel_0(X24,X23)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | m1_subset_1(k2_waybel_0(X23,X24,X25),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_waybel_0])])])).

cnf(c_0_46,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,X1)
    | ~ r2_hidden(k4_yellow_6(esk7_0,esk8_0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_14]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_24]),c_0_23])).

cnf(c_0_47,plain,
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
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
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
    | ~ m1_subset_1(X3,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk7_0,esk8_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_21]),c_0_24]),c_0_23]),c_0_22])])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,esk4_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk7_0,esk8_0)))
    | r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_14]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_24]),c_0_23])).

cnf(c_0_54,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,esk4_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk7_0,esk8_0)))
    | r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_19]),c_0_20]),c_0_21]),c_0_56]),c_0_16]),c_0_57])]),c_0_58]),c_0_23]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:39:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.031 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t42_yellow_6, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_6)).
% 0.19/0.39  fof(t25_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>k2_waybel_0(X1,X2,X3)=k4_yellow_6(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_6)).
% 0.19/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.39  fof(d11_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r2_hidden(k2_waybel_0(X1,X2,X5),X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 0.19/0.39  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.19/0.39  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.19/0.39  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.19/0.39  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.19/0.39  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.19/0.39  fof(dt_k2_waybel_0, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))&m1_subset_1(X3,u1_struct_0(X2)))=>m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))))), inference(assume_negation,[status(cth)],[t42_yellow_6])).
% 0.19/0.39  fof(c_0_11, plain, ![X37, X38, X39]:(v2_struct_0(X37)|~l1_struct_0(X37)|(v2_struct_0(X38)|~v4_orders_2(X38)|~v7_waybel_0(X38)|~v1_yellow_6(X38,X37)|~l1_waybel_0(X38,X37)|(~m1_subset_1(X39,u1_struct_0(X38))|k2_waybel_0(X37,X38,X39)=k4_yellow_6(X37,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow_6])])])])).
% 0.19/0.39  fof(c_0_12, plain, ![X8]:(~l1_pre_topc(X8)|l1_struct_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.39  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk7_0)&v2_pre_topc(esk7_0))&l1_pre_topc(esk7_0))&(((((~v2_struct_0(esk8_0)&v4_orders_2(esk8_0))&v7_waybel_0(esk8_0))&v1_yellow_6(esk8_0,esk7_0))&l1_waybel_0(esk8_0,esk7_0))&~r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.39  cnf(c_0_14, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_waybel_0(X1,X2,X3)=k4_yellow_6(X1,X2)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v1_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_15, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_17, plain, (k2_waybel_0(X1,X2,X3)=k2_waybel_0(X1,X2,X4)|v2_struct_0(X1)|v2_struct_0(X2)|~v1_yellow_6(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_14, c_0_14])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (v1_yellow_6(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (v7_waybel_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (v4_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_22, negated_conjecture, (l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  fof(c_0_25, plain, ![X15, X16, X17, X19, X20, X21]:(((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X16))|~r1_waybel_0(X15,X16,X17)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&(~m1_subset_1(X19,u1_struct_0(X16))|(~r1_orders_2(X16,esk2_3(X15,X16,X17),X19)|r2_hidden(k2_waybel_0(X15,X16,X19),X17))|~r1_waybel_0(X15,X16,X17)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15))))&((m1_subset_1(esk3_4(X15,X16,X20,X21),u1_struct_0(X16))|~m1_subset_1(X21,u1_struct_0(X16))|r1_waybel_0(X15,X16,X20)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&((r1_orders_2(X16,X21,esk3_4(X15,X16,X20,X21))|~m1_subset_1(X21,u1_struct_0(X16))|r1_waybel_0(X15,X16,X20)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&(~r2_hidden(k2_waybel_0(X15,X16,esk3_4(X15,X16,X20,X21)),X20)|~m1_subset_1(X21,u1_struct_0(X16))|r1_waybel_0(X15,X16,X20)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (k2_waybel_0(esk7_0,esk8_0,X1)=k2_waybel_0(esk7_0,esk8_0,X2)|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.19/0.39  fof(c_0_27, plain, ![X6]:m1_subset_1(esk1_1(X6),X6), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.19/0.39  cnf(c_0_28, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_29, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (k2_waybel_0(esk7_0,esk8_0,X1)=k4_yellow_6(esk7_0,esk8_0)|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_26]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_24]), c_0_23])).
% 0.19/0.39  cnf(c_0_31, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  fof(c_0_32, plain, ![X12, X13, X14]:(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(~m1_subset_1(X14,u1_struct_0(X12))|(~m1_connsp_2(X13,X12,X14)|r2_hidden(X14,X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.19/0.39  fof(c_0_33, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)|~m1_subset_1(X10,u1_struct_0(X9))|(~m1_connsp_2(X11,X9,X10)|m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.19/0.39  fof(c_0_34, plain, ![X26, X27, X28, X29, X30, X34]:(((~r2_hidden(X29,X28)|(~m1_connsp_2(X30,X26,X29)|r1_waybel_0(X26,X27,X30))|~m1_subset_1(X29,u1_struct_0(X26))|X28!=k10_yellow_6(X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&((m1_connsp_2(esk4_4(X26,X27,X28,X29),X26,X29)|r2_hidden(X29,X28)|~m1_subset_1(X29,u1_struct_0(X26))|X28!=k10_yellow_6(X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r1_waybel_0(X26,X27,esk4_4(X26,X27,X28,X29))|r2_hidden(X29,X28)|~m1_subset_1(X29,u1_struct_0(X26))|X28!=k10_yellow_6(X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))))&((m1_subset_1(esk5_3(X26,X27,X28),u1_struct_0(X26))|X28=k10_yellow_6(X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(((m1_connsp_2(esk6_3(X26,X27,X28),X26,esk5_3(X26,X27,X28))|~r2_hidden(esk5_3(X26,X27,X28),X28)|X28=k10_yellow_6(X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r1_waybel_0(X26,X27,esk6_3(X26,X27,X28))|~r2_hidden(esk5_3(X26,X27,X28),X28)|X28=k10_yellow_6(X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))))&(r2_hidden(esk5_3(X26,X27,X28),X28)|(~m1_connsp_2(X34,X26,esk5_3(X26,X27,X28))|r1_waybel_0(X26,X27,X34))|X28=k10_yellow_6(X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.19/0.39  fof(c_0_35, plain, ![X35, X36]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|v2_struct_0(X36)|~v4_orders_2(X36)|~v7_waybel_0(X36)|~l1_waybel_0(X36,X35)|m1_subset_1(k10_yellow_6(X35,X36),k1_zfmisc_1(u1_struct_0(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.19/0.39  cnf(c_0_36, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|~v1_yellow_6(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,X1)|~r2_hidden(k4_yellow_6(X1,X2),X3)|~l1_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_14]), c_0_29])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (k2_waybel_0(esk7_0,esk8_0,X1)=k4_yellow_6(esk7_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.39  cnf(c_0_38, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_39, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_40, plain, (m1_connsp_2(esk4_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,X1)|~r2_hidden(k2_waybel_0(esk7_0,esk8_0,X2),X1)|~m1_subset_1(X3,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.19/0.39  cnf(c_0_43, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~m1_connsp_2(X2,X3,X1)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.39  cnf(c_0_44, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|m1_connsp_2(esk4_4(X2,X3,k10_yellow_6(X2,X3),X1),X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_41])).
% 0.19/0.39  fof(c_0_45, plain, ![X23, X24, X25]:(v2_struct_0(X23)|~l1_struct_0(X23)|v2_struct_0(X24)|~l1_waybel_0(X24,X23)|~m1_subset_1(X25,u1_struct_0(X24))|m1_subset_1(k2_waybel_0(X23,X24,X25),u1_struct_0(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_waybel_0])])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,X1)|~r2_hidden(k4_yellow_6(esk7_0,esk8_0),X1)|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X3,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_14]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_24]), c_0_23])).
% 0.19/0.39  cnf(c_0_47, plain, (r2_hidden(X1,esk4_4(X2,X3,k10_yellow_6(X2,X3),X1))|r2_hidden(X1,k10_yellow_6(X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.39  cnf(c_0_48, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,esk4_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk7_0,esk8_0)))|r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(esk8_0))|~m1_subset_1(X4,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(k2_waybel_0(esk7_0,esk8_0,X1),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_21]), c_0_24]), c_0_23]), c_0_22])])).
% 0.19/0.39  cnf(c_0_51, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,esk4_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk7_0,esk8_0)))|r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_49, c_0_31])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_14]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_24]), c_0_23])).
% 0.19/0.39  cnf(c_0_54, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~r1_waybel_0(X2,X3,esk4_4(X2,X3,k10_yellow_6(X2,X3),X1))|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]), c_0_41])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,esk4_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk7_0,esk8_0)))|r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_52, c_0_31])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(k4_yellow_6(esk7_0,esk8_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_53, c_0_31])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (~r2_hidden(k4_yellow_6(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_19]), c_0_20]), c_0_21]), c_0_56]), c_0_16]), c_0_57])]), c_0_58]), c_0_23]), c_0_24]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 60
% 0.19/0.39  # Proof object clause steps            : 39
% 0.19/0.39  # Proof object formula steps           : 21
% 0.19/0.39  # Proof object conjectures             : 25
% 0.19/0.39  # Proof object clause conjectures      : 22
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 20
% 0.19/0.39  # Proof object initial formulas used   : 10
% 0.19/0.39  # Proof object generating inferences   : 16
% 0.19/0.39  # Proof object simplifying inferences  : 59
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 10
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 28
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 28
% 0.19/0.39  # Processed clauses                    : 129
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 30
% 0.19/0.39  # ...remaining for further processing  : 99
% 0.19/0.39  # Other redundant clauses eliminated   : 3
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 9
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 117
% 0.19/0.39  # ...of the previous two non-trivial   : 104
% 0.19/0.39  # Contextual simplify-reflections      : 9
% 0.19/0.39  # Paramodulations                      : 114
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 3
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 58
% 0.19/0.39  #    Positive orientable unit clauses  : 9
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 3
% 0.19/0.39  #    Non-unit-clauses                  : 46
% 0.19/0.39  # Current number of unprocessed clauses: 25
% 0.19/0.39  # ...number of literals in the above   : 396
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 38
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1938
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 103
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 46
% 0.19/0.39  # Unit Clause-clause subsumption calls : 20
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 1
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 9033
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.053 s
% 0.19/0.39  # System time              : 0.006 s
% 0.19/0.39  # Total time               : 0.059 s
% 0.19/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
