%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:15 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 132 expanded)
%              Number of clauses        :   33 (  54 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  217 ( 753 expanded)
%              Number of equality atoms :   18 (  72 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t29_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(t9_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ~ r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_k4_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(existence_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ? [X2] : l1_waybel_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_l1_waybel_0)).

fof(c_0_9,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t29_yellow_6])).

fof(c_0_11,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r1_waybel_0(X30,X31,X32)
        | ~ r2_waybel_0(X30,X31,k6_subset_1(u1_struct_0(X30),X32))
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30) )
      & ( r2_waybel_0(X30,X31,k6_subset_1(u1_struct_0(X30),X32))
        | r1_waybel_0(X30,X31,X32)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).

fof(c_0_12,plain,(
    ! [X15,X16] : k6_subset_1(X15,X16) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21,X23,X25] :
      ( ( m1_subset_1(esk2_4(X18,X19,X20,X21),u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ r2_waybel_0(X18,X19,X20)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) )
      & ( r1_orders_2(X19,X21,esk2_4(X18,X19,X20,X21))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ r2_waybel_0(X18,X19,X20)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) )
      & ( r2_hidden(k2_waybel_0(X18,X19,esk2_4(X18,X19,X20,X21)),X20)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ r2_waybel_0(X18,X19,X20)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) )
      & ( m1_subset_1(esk3_3(X18,X19,X23),u1_struct_0(X19))
        | r2_waybel_0(X18,X19,X23)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X19))
        | ~ r1_orders_2(X19,esk3_3(X18,X19,X23),X25)
        | ~ r2_hidden(k2_waybel_0(X18,X19,X25),X23)
        | r2_waybel_0(X18,X19,X23)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_struct_0(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v4_orders_2(esk6_0)
    & v7_waybel_0(esk6_0)
    & l1_waybel_0(esk6_0,esk5_0)
    & ~ r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_19,plain,
    ( r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_waybel_0(X1,X2,X3)
    | r2_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X3)
    | ~ r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X3)
    | r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_33,plain,(
    ! [X26,X27] :
      ( ~ l1_struct_0(X26)
      | ~ l1_waybel_0(X27,X26)
      | l1_orders_2(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,k4_xboole_0(X4,X5))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,k4_xboole_0(X4,X5),X3)),X5) ),
    inference(spm,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,k4_xboole_0(X3,X4),X5)),X3)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,k4_xboole_0(X3,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_38,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_39,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_waybel_0(X2,X1,k4_xboole_0(X4,X4))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ l1_struct_0(X33)
      | ~ l1_waybel_0(X34,X33)
      | m1_subset_1(k4_yellow_6(X33,X34),u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).

cnf(c_0_43,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_28])])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_48,plain,(
    ! [X28] :
      ( ~ l1_struct_0(X28)
      | l1_waybel_0(esk4_1(X28),X28) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[existence_l1_waybel_0])])])).

cnf(c_0_49,negated_conjecture,
    ( ~ l1_waybel_0(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),c_0_29])).

cnf(c_0_50,plain,
    ( l1_waybel_0(esk4_1(X1),X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:26:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.015 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.41  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.19/0.41  fof(t9_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>~(r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_waybel_0)).
% 0.19/0.41  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.19/0.41  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.19/0.41  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.19/0.41  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.41  fof(dt_k4_yellow_6, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_struct_0(X1))&l1_waybel_0(X2,X1))=>m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 0.19/0.41  fof(existence_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>?[X2]:l1_waybel_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_l1_waybel_0)).
% 0.19/0.41  fof(c_0_9, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.41  fof(c_0_10, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.19/0.41  fof(c_0_11, plain, ![X30, X31, X32]:((~r1_waybel_0(X30,X31,X32)|~r2_waybel_0(X30,X31,k6_subset_1(u1_struct_0(X30),X32))|(v2_struct_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~l1_struct_0(X30)))&(r2_waybel_0(X30,X31,k6_subset_1(u1_struct_0(X30),X32))|r1_waybel_0(X30,X31,X32)|(v2_struct_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~l1_struct_0(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).
% 0.19/0.41  fof(c_0_12, plain, ![X15, X16]:k6_subset_1(X15,X16)=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.19/0.41  cnf(c_0_13, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_15, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  fof(c_0_17, plain, ![X18, X19, X20, X21, X23, X25]:((((m1_subset_1(esk2_4(X18,X19,X20,X21),u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~r2_waybel_0(X18,X19,X20)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18)))&(r1_orders_2(X19,X21,esk2_4(X18,X19,X20,X21))|~m1_subset_1(X21,u1_struct_0(X19))|~r2_waybel_0(X18,X19,X20)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18))))&(r2_hidden(k2_waybel_0(X18,X19,esk2_4(X18,X19,X20,X21)),X20)|~m1_subset_1(X21,u1_struct_0(X19))|~r2_waybel_0(X18,X19,X20)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18))))&((m1_subset_1(esk3_3(X18,X19,X23),u1_struct_0(X19))|r2_waybel_0(X18,X19,X23)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18)))&(~m1_subset_1(X25,u1_struct_0(X19))|~r1_orders_2(X19,esk3_3(X18,X19,X23),X25)|~r2_hidden(k2_waybel_0(X18,X19,X25),X23)|r2_waybel_0(X18,X19,X23)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.19/0.41  fof(c_0_18, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_struct_0(esk5_0))&((((~v2_struct_0(esk6_0)&v4_orders_2(esk6_0))&v7_waybel_0(esk6_0))&l1_waybel_0(esk6_0,esk5_0))&~r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.41  cnf(c_0_19, plain, (r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_20, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_21, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_22, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.41  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_24, plain, (r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (~r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_26, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r1_waybel_0(X1,X2,X3)|r2_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X3)|~r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.41  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X3)|r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.19/0.41  fof(c_0_33, plain, ![X26, X27]:(~l1_struct_0(X26)|(~l1_waybel_0(X27,X26)|l1_orders_2(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.19/0.41  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~r2_waybel_0(X1,X2,k4_xboole_0(X4,X5))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,k4_xboole_0(X4,X5),X3)),X5)), inference(spm,[status(thm)],[c_0_21, c_0_24])).
% 0.19/0.41  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,k4_xboole_0(X3,X4),X5)),X3)|~m1_subset_1(X5,u1_struct_0(X2))|~r2_waybel_0(X1,X2,k4_xboole_0(X3,X4))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.19/0.41  cnf(c_0_37, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.41  fof(c_0_38, plain, ![X17]:(~l1_orders_2(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.41  cnf(c_0_39, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_40, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_waybel_0(X2,X1,k4_xboole_0(X4,X4))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.41  fof(c_0_42, plain, ![X33, X34]:(v2_struct_0(X33)|~l1_struct_0(X33)|~l1_waybel_0(X34,X33)|m1_subset_1(k4_yellow_6(X33,X34),u1_struct_0(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).
% 0.19/0.41  cnf(c_0_43, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (l1_orders_2(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_27]), c_0_28])])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.19/0.41  cnf(c_0_46, plain, (v2_struct_0(X1)|m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.41  fof(c_0_48, plain, ![X28]:(~l1_struct_0(X28)|l1_waybel_0(esk4_1(X28),X28)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[existence_l1_waybel_0])])])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (~l1_waybel_0(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), c_0_29])).
% 0.19/0.41  cnf(c_0_50, plain, (l1_waybel_0(esk4_1(X1),X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_47])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 52
% 0.19/0.41  # Proof object clause steps            : 33
% 0.19/0.41  # Proof object formula steps           : 19
% 0.19/0.41  # Proof object conjectures             : 15
% 0.19/0.41  # Proof object clause conjectures      : 12
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 16
% 0.19/0.41  # Proof object initial formulas used   : 9
% 0.19/0.41  # Proof object generating inferences   : 16
% 0.19/0.41  # Proof object simplifying inferences  : 18
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 9
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 25
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 24
% 0.19/0.41  # Processed clauses                    : 1956
% 0.19/0.41  # ...of these trivial                  : 29
% 0.19/0.41  # ...subsumed                          : 1739
% 0.19/0.41  # ...remaining for further processing  : 188
% 0.19/0.41  # Other redundant clauses eliminated   : 25
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 3
% 0.19/0.41  # Backward-rewritten                   : 1
% 0.19/0.41  # Generated clauses                    : 7473
% 0.19/0.41  # ...of the previous two non-trivial   : 6277
% 0.19/0.41  # Contextual simplify-reflections      : 5
% 0.19/0.41  # Paramodulations                      : 7418
% 0.19/0.41  # Factorizations                       : 16
% 0.19/0.41  # Equation resolutions                 : 39
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 160
% 0.19/0.41  #    Positive orientable unit clauses  : 24
% 0.19/0.41  #    Positive unorientable unit clauses: 5
% 0.19/0.41  #    Negative unit clauses             : 12
% 0.19/0.41  #    Non-unit-clauses                  : 119
% 0.19/0.41  # Current number of unprocessed clauses: 4368
% 0.19/0.41  # ...number of literals in the above   : 13905
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 29
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 10515
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 5395
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 910
% 0.19/0.41  # Unit Clause-clause subsumption calls : 502
% 0.19/0.41  # Rewrite failures with RHS unbound    : 278
% 0.19/0.41  # BW rewrite match attempts            : 440
% 0.19/0.41  # BW rewrite match successes           : 31
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 90292
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.076 s
% 0.19/0.41  # System time              : 0.003 s
% 0.19/0.41  # Total time               : 0.079 s
% 0.19/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
