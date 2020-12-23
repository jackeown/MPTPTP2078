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
% DateTime   : Thu Dec  3 11:21:20 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 173 expanded)
%              Number of clauses        :   26 (  52 expanded)
%              Number of leaves         :    8 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  248 (1296 expanded)
%              Number of equality atoms :   13 ( 115 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_yellow_6)).

fof(dt_k2_waybel_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( v2_struct_0(X7)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X8)
      | ~ l1_waybel_0(X8,X7)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | m1_subset_1(k2_waybel_0(X7,X8,X9),u1_struct_0(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_waybel_0])])])).

fof(c_0_10,plain,(
    ! [X4] : m1_subset_1(esk1_1(X4),X4) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ l1_struct_0(X15)
      | v2_struct_0(X16)
      | ~ v4_orders_2(X16)
      | ~ v7_waybel_0(X16)
      | ~ v1_yellow_6(X16,X15)
      | ~ l1_waybel_0(X16,X15)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | k2_waybel_0(X15,X16,X17) = k4_yellow_6(X15,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow_6])])])])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(X19)
      | ~ v4_orders_2(X19)
      | ~ v7_waybel_0(X19)
      | ~ v1_yellow_6(X19,X18)
      | ~ l1_waybel_0(X19,X18)
      | r2_hidden(k4_yellow_6(X18,X19),k10_yellow_6(X18,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_6])])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v8_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v4_orders_2(esk3_0)
    & v7_waybel_0(esk3_0)
    & v1_yellow_6(esk3_0,esk2_0)
    & l1_waybel_0(esk3_0,esk2_0)
    & k11_yellow_6(esk2_0,esk3_0) != k4_yellow_6(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_14,plain,(
    ! [X10,X11] :
      ( ( ~ v2_struct_0(X11)
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ v1_yellow_6(X11,X10)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v4_orders_2(X11)
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ v1_yellow_6(X11,X10)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v7_waybel_0(X11)
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ v1_yellow_6(X11,X10)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v3_yellow_6(X11,X10)
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ v1_yellow_6(X11,X10)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_yellow_6])])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

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
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ( X14 != k11_yellow_6(X12,X13)
        | r2_hidden(X14,k10_yellow_6(X12,X13))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ v3_yellow_6(X13,X12)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v8_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(X14,k10_yellow_6(X12,X13))
        | X14 = k11_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ v3_yellow_6(X13,X12)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v8_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_yellow_6])])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_yellow_6(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v7_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
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

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k2_waybel_0(X1,X2,esk1_1(u1_struct_0(X2))),u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_30,plain,
    ( k2_waybel_0(X1,X2,esk1_1(u1_struct_0(X2))) = k4_yellow_6(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_31,plain,
    ( X1 = k11_yellow_6(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k10_yellow_6(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ v3_yellow_6(X3,X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ v8_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk2_0,esk3_0),k10_yellow_6(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v8_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( v3_yellow_6(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_27]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k11_yellow_6(esk2_0,esk3_0) != k4_yellow_6(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk2_0,esk3_0,esk1_1(u1_struct_0(esk3_0))),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_27]),c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( k2_waybel_0(esk2_0,esk3_0,esk1_1(u1_struct_0(esk3_0))) = k4_yellow_6(esk2_0,esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21]),c_0_22]),c_0_24])]),c_0_27]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(k4_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_35]),c_0_26]),c_0_27])).

fof(c_0_39,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_40,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:58:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t45_yellow_6, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>k11_yellow_6(X1,X2)=k4_yellow_6(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_yellow_6)).
% 0.13/0.37  fof(dt_k2_waybel_0, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))&m1_subset_1(X3,u1_struct_0(X2)))=>m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 0.13/0.37  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.13/0.37  fof(t25_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>k2_waybel_0(X1,X2,X3)=k4_yellow_6(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_6)).
% 0.13/0.37  fof(t42_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_6)).
% 0.13/0.37  fof(cc4_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(l1_waybel_0(X2,X1)=>((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))=>(((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_yellow_6)).
% 0.13/0.37  fof(d20_yellow_6, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k11_yellow_6(X1,X2)<=>r2_hidden(X3,k10_yellow_6(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_yellow_6)).
% 0.13/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v1_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>k11_yellow_6(X1,X2)=k4_yellow_6(X1,X2)))), inference(assume_negation,[status(cth)],[t45_yellow_6])).
% 0.13/0.37  fof(c_0_9, plain, ![X7, X8, X9]:(v2_struct_0(X7)|~l1_struct_0(X7)|v2_struct_0(X8)|~l1_waybel_0(X8,X7)|~m1_subset_1(X9,u1_struct_0(X8))|m1_subset_1(k2_waybel_0(X7,X8,X9),u1_struct_0(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_waybel_0])])])).
% 0.13/0.37  fof(c_0_10, plain, ![X4]:m1_subset_1(esk1_1(X4),X4), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.13/0.37  fof(c_0_11, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~l1_struct_0(X15)|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~v1_yellow_6(X16,X15)|~l1_waybel_0(X16,X15)|(~m1_subset_1(X17,u1_struct_0(X16))|k2_waybel_0(X15,X16,X17)=k4_yellow_6(X15,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow_6])])])])).
% 0.13/0.37  fof(c_0_12, plain, ![X18, X19]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(v2_struct_0(X19)|~v4_orders_2(X19)|~v7_waybel_0(X19)|~v1_yellow_6(X19,X18)|~l1_waybel_0(X19,X18)|r2_hidden(k4_yellow_6(X18,X19),k10_yellow_6(X18,X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_6])])])])).
% 0.13/0.37  fof(c_0_13, negated_conjecture, ((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v8_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((((~v2_struct_0(esk3_0)&v4_orders_2(esk3_0))&v7_waybel_0(esk3_0))&v1_yellow_6(esk3_0,esk2_0))&l1_waybel_0(esk3_0,esk2_0))&k11_yellow_6(esk2_0,esk3_0)!=k4_yellow_6(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.13/0.37  fof(c_0_14, plain, ![X10, X11]:((((~v2_struct_0(X11)|(v2_struct_0(X11)|~v4_orders_2(X11)|~v7_waybel_0(X11)|~v1_yellow_6(X11,X10))|~l1_waybel_0(X11,X10)|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(v4_orders_2(X11)|(v2_struct_0(X11)|~v4_orders_2(X11)|~v7_waybel_0(X11)|~v1_yellow_6(X11,X10))|~l1_waybel_0(X11,X10)|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v7_waybel_0(X11)|(v2_struct_0(X11)|~v4_orders_2(X11)|~v7_waybel_0(X11)|~v1_yellow_6(X11,X10))|~l1_waybel_0(X11,X10)|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v3_yellow_6(X11,X10)|(v2_struct_0(X11)|~v4_orders_2(X11)|~v7_waybel_0(X11)|~v1_yellow_6(X11,X10))|~l1_waybel_0(X11,X10)|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_yellow_6])])])])])).
% 0.13/0.37  cnf(c_0_15, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_16, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_17, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_waybel_0(X1,X2,X3)=k4_yellow_6(X1,X2)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v1_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  fof(c_0_18, plain, ![X12, X13, X14]:((X14!=k11_yellow_6(X12,X13)|r2_hidden(X14,k10_yellow_6(X12,X13))|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~v3_yellow_6(X13,X12)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~v8_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(X14,k10_yellow_6(X12,X13))|X14=k11_yellow_6(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~v3_yellow_6(X13,X12)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~v8_pre_topc(X12)|~l1_pre_topc(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_yellow_6])])])])])).
% 0.13/0.37  cnf(c_0_19, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v1_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (v1_yellow_6(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (v7_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (l1_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_28, plain, (v3_yellow_6(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~v1_yellow_6(X1,X2)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_29, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k2_waybel_0(X1,X2,esk1_1(u1_struct_0(X2))),u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.37  cnf(c_0_30, plain, (k2_waybel_0(X1,X2,esk1_1(u1_struct_0(X2)))=k4_yellow_6(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~v1_yellow_6(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.13/0.37  cnf(c_0_31, plain, (X1=k11_yellow_6(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|~r2_hidden(X1,k10_yellow_6(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~v3_yellow_6(X3,X2)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~v8_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_yellow_6(esk2_0,esk3_0),k10_yellow_6(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26]), c_0_27])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (v8_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (v3_yellow_6(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_27]), c_0_26])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (k11_yellow_6(esk2_0,esk3_0)!=k4_yellow_6(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (m1_subset_1(k2_waybel_0(esk2_0,esk3_0,esk1_1(u1_struct_0(esk3_0))),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_27]), c_0_26])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (k2_waybel_0(esk2_0,esk3_0,esk1_1(u1_struct_0(esk3_0)))=k4_yellow_6(esk2_0,esk3_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_20]), c_0_21]), c_0_22]), c_0_24])]), c_0_27]), c_0_26])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (~m1_subset_1(k4_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_35]), c_0_26]), c_0_27])).
% 0.13/0.37  fof(c_0_39, plain, ![X6]:(~l1_pre_topc(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.13/0.37  cnf(c_0_41, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_25])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 43
% 0.13/0.37  # Proof object clause steps            : 26
% 0.13/0.37  # Proof object formula steps           : 17
% 0.13/0.37  # Proof object conjectures             : 20
% 0.13/0.37  # Proof object clause conjectures      : 17
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 17
% 0.13/0.37  # Proof object initial formulas used   : 8
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 38
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 8
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 21
% 0.13/0.37  # Removed in clause preprocessing      : 3
% 0.13/0.37  # Initial clauses in saturation        : 18
% 0.13/0.37  # Processed clauses                    : 48
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 48
% 0.13/0.37  # Other redundant clauses eliminated   : 1
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 13
% 0.13/0.37  # ...of the previous two non-trivial   : 12
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 12
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 1
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 28
% 0.13/0.37  #    Positive orientable unit clauses  : 10
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 5
% 0.13/0.37  #    Non-unit-clauses                  : 13
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 19
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 33
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 5
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 12
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2774
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.031 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
