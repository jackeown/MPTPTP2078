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
% DateTime   : Thu Dec  3 11:21:13 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 399 expanded)
%              Number of clauses        :   37 ( 160 expanded)
%              Number of leaves         :    7 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  231 (2128 expanded)
%              Number of equality atoms :   17 (  98 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_7,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X23,X24,X25,X26,X28,X30] :
      ( ( m1_subset_1(esk3_4(X23,X24,X25,X26),u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ r2_waybel_0(X23,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) )
      & ( r1_orders_2(X24,X26,esk3_4(X23,X24,X25,X26))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ r2_waybel_0(X23,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) )
      & ( r2_hidden(k2_waybel_0(X23,X24,esk3_4(X23,X24,X25,X26)),X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ r2_waybel_0(X23,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) )
      & ( m1_subset_1(esk4_3(X23,X24,X28),u1_struct_0(X24))
        | r2_waybel_0(X23,X24,X28)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X24))
        | ~ r1_orders_2(X24,esk4_3(X23,X24,X28),X30)
        | ~ r2_hidden(k2_waybel_0(X23,X24,X30),X28)
        | r2_waybel_0(X23,X24,X28)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

fof(c_0_9,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X20,X19)
        | r2_hidden(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ r2_hidden(X20,X19)
        | m1_subset_1(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ m1_subset_1(X20,X19)
        | v1_xboole_0(X20)
        | ~ v1_xboole_0(X19) )
      & ( ~ v1_xboole_0(X20)
        | m1_subset_1(X20,X19)
        | ~ v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_10,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r1_waybel_0(X31,X32,X33)
        | ~ r2_waybel_0(X31,X32,k6_subset_1(u1_struct_0(X31),X33))
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31) )
      & ( r2_waybel_0(X31,X32,k6_subset_1(u1_struct_0(X31),X33))
        | r1_waybel_0(X31,X32,X33)
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).

fof(c_0_15,plain,(
    ! [X21,X22] : k6_subset_1(X21,X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_16,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X13,X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X15)
        | r2_hidden(esk2_3(X15,X16,X17),X16)
        | X17 = k4_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X15)
        | r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X16)
        | r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k4_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_12,c_0_10])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_struct_0(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v4_orders_2(esk6_0)
    & v7_waybel_0(esk6_0)
    & l1_waybel_0(esk6_0,esk5_0)
    & ~ r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_20,plain,
    ( r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X2,X1,X3)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_waybel_0(X1,X2,X3)
    | r2_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_xboole_0(u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X1)
    | v1_xboole_0(k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | ~ v1_xboole_0(k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_28]),c_0_29])]),c_0_31]),c_0_30])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_44,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk6_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk6_0) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r2_waybel_0(X1,esk6_0,X2)
    | ~ l1_waybel_0(esk6_0,X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_47]),c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_28]),c_0_29]),c_0_43])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.30  % Computer   : n025.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 17:38:05 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  # Version: 2.5pre002
% 0.11/0.30  # No SInE strategy applied
% 0.11/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.34  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.15/0.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.34  #
% 0.15/0.34  # Preprocessing time       : 0.029 s
% 0.15/0.34  # Presaturation interreduction done
% 0.15/0.34  
% 0.15/0.34  # Proof found!
% 0.15/0.34  # SZS status Theorem
% 0.15/0.34  # SZS output start CNFRefutation
% 0.15/0.34  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.15/0.34  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.15/0.34  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.15/0.34  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.15/0.34  fof(t9_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>~(r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_waybel_0)).
% 0.15/0.34  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.15/0.34  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.15/0.34  fof(c_0_7, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.15/0.34  fof(c_0_8, plain, ![X23, X24, X25, X26, X28, X30]:((((m1_subset_1(esk3_4(X23,X24,X25,X26),u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))|~r2_waybel_0(X23,X24,X25)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23)))&(r1_orders_2(X24,X26,esk3_4(X23,X24,X25,X26))|~m1_subset_1(X26,u1_struct_0(X24))|~r2_waybel_0(X23,X24,X25)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23))))&(r2_hidden(k2_waybel_0(X23,X24,esk3_4(X23,X24,X25,X26)),X25)|~m1_subset_1(X26,u1_struct_0(X24))|~r2_waybel_0(X23,X24,X25)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23))))&((m1_subset_1(esk4_3(X23,X24,X28),u1_struct_0(X24))|r2_waybel_0(X23,X24,X28)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23)))&(~m1_subset_1(X30,u1_struct_0(X24))|~r1_orders_2(X24,esk4_3(X23,X24,X28),X30)|~r2_hidden(k2_waybel_0(X23,X24,X30),X28)|r2_waybel_0(X23,X24,X28)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.15/0.34  fof(c_0_9, plain, ![X19, X20]:(((~m1_subset_1(X20,X19)|r2_hidden(X20,X19)|v1_xboole_0(X19))&(~r2_hidden(X20,X19)|m1_subset_1(X20,X19)|v1_xboole_0(X19)))&((~m1_subset_1(X20,X19)|v1_xboole_0(X20)|~v1_xboole_0(X19))&(~v1_xboole_0(X20)|m1_subset_1(X20,X19)|~v1_xboole_0(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.15/0.34  cnf(c_0_10, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.34  cnf(c_0_11, plain, (r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.34  cnf(c_0_12, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.34  fof(c_0_13, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.15/0.34  fof(c_0_14, plain, ![X31, X32, X33]:((~r1_waybel_0(X31,X32,X33)|~r2_waybel_0(X31,X32,k6_subset_1(u1_struct_0(X31),X33))|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~l1_struct_0(X31)))&(r2_waybel_0(X31,X32,k6_subset_1(u1_struct_0(X31),X33))|r1_waybel_0(X31,X32,X33)|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~l1_struct_0(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).
% 0.15/0.34  fof(c_0_15, plain, ![X21, X22]:k6_subset_1(X21,X22)=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.15/0.34  fof(c_0_16, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:((((r2_hidden(X13,X10)|~r2_hidden(X13,X12)|X12!=k4_xboole_0(X10,X11))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|X12!=k4_xboole_0(X10,X11)))&(~r2_hidden(X14,X10)|r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k4_xboole_0(X10,X11)))&((~r2_hidden(esk2_3(X15,X16,X17),X17)|(~r2_hidden(esk2_3(X15,X16,X17),X15)|r2_hidden(esk2_3(X15,X16,X17),X16))|X17=k4_xboole_0(X15,X16))&((r2_hidden(esk2_3(X15,X16,X17),X15)|r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k4_xboole_0(X15,X16))&(~r2_hidden(esk2_3(X15,X16,X17),X16)|r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k4_xboole_0(X15,X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.15/0.34  cnf(c_0_17, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.15/0.34  cnf(c_0_18, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_12, c_0_10])).
% 0.15/0.34  fof(c_0_19, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_struct_0(esk5_0))&((((~v2_struct_0(esk6_0)&v4_orders_2(esk6_0))&v7_waybel_0(esk6_0))&l1_waybel_0(esk6_0,esk5_0))&~r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.15/0.34  cnf(c_0_20, plain, (r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.34  cnf(c_0_21, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.34  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.34  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.34  cnf(c_0_24, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X2,X1,X3)|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~r2_hidden(X4,u1_struct_0(X1))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.15/0.34  cnf(c_0_25, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.34  cnf(c_0_26, negated_conjecture, (~r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.34  cnf(c_0_27, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r1_waybel_0(X1,X2,X3)|r2_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.15/0.34  cnf(c_0_28, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.34  cnf(c_0_29, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.34  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.34  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.34  cnf(c_0_32, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_22])).
% 0.15/0.34  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_23])).
% 0.15/0.34  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v1_xboole_0(u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.15/0.34  cnf(c_0_35, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), c_0_31])).
% 0.15/0.34  cnf(c_0_36, plain, (v1_xboole_0(k4_xboole_0(X1,X2))|~r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_32, c_0_25])).
% 0.15/0.34  cnf(c_0_37, plain, (r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X1)|v1_xboole_0(k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_25])).
% 0.15/0.34  cnf(c_0_38, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|~v1_xboole_0(k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_28]), c_0_29])]), c_0_31]), c_0_30])).
% 0.15/0.34  cnf(c_0_39, plain, (v1_xboole_0(k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.15/0.34  cnf(c_0_40, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.34  cnf(c_0_41, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.34  cnf(c_0_42, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.34  cnf(c_0_43, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.15/0.34  cnf(c_0_44, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.15/0.34  cnf(c_0_45, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk6_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.15/0.34  cnf(c_0_46, plain, (X1=k4_xboole_0(X2,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_10, c_0_44])).
% 0.15/0.34  cnf(c_0_47, negated_conjecture, (m1_subset_1(u1_struct_0(esk6_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_43])).
% 0.15/0.34  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk6_0)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_46, c_0_43])).
% 0.15/0.34  cnf(c_0_49, negated_conjecture, (v2_struct_0(X1)|~r2_waybel_0(X1,esk6_0,X2)|~l1_waybel_0(esk6_0,X1)|~l1_struct_0(X1)|~v1_xboole_0(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_47]), c_0_30])).
% 0.15/0.34  cnf(c_0_50, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_35, c_0_48])).
% 0.15/0.34  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_28]), c_0_29]), c_0_43])]), c_0_31]), ['proof']).
% 0.15/0.34  # SZS output end CNFRefutation
% 0.15/0.34  # Proof object total steps             : 52
% 0.15/0.34  # Proof object clause steps            : 37
% 0.15/0.34  # Proof object formula steps           : 15
% 0.15/0.34  # Proof object conjectures             : 17
% 0.15/0.34  # Proof object clause conjectures      : 14
% 0.15/0.34  # Proof object formula conjectures     : 3
% 0.15/0.34  # Proof object initial clauses used    : 16
% 0.15/0.34  # Proof object initial formulas used   : 7
% 0.15/0.34  # Proof object generating inferences   : 17
% 0.15/0.34  # Proof object simplifying inferences  : 21
% 0.15/0.34  # Training examples: 0 positive, 0 negative
% 0.15/0.34  # Parsed axioms                        : 7
% 0.15/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.34  # Initial clauses                      : 27
% 0.15/0.34  # Removed in clause preprocessing      : 1
% 0.15/0.34  # Initial clauses in saturation        : 26
% 0.15/0.34  # Processed clauses                    : 168
% 0.15/0.34  # ...of these trivial                  : 2
% 0.15/0.34  # ...subsumed                          : 58
% 0.15/0.34  # ...remaining for further processing  : 108
% 0.15/0.34  # Other redundant clauses eliminated   : 5
% 0.15/0.34  # Clauses deleted for lack of memory   : 0
% 0.15/0.34  # Backward-subsumed                    : 2
% 0.15/0.34  # Backward-rewritten                   : 3
% 0.15/0.34  # Generated clauses                    : 335
% 0.15/0.34  # ...of the previous two non-trivial   : 260
% 0.15/0.34  # Contextual simplify-reflections      : 3
% 0.15/0.34  # Paramodulations                      : 321
% 0.15/0.34  # Factorizations                       : 2
% 0.15/0.34  # Equation resolutions                 : 12
% 0.15/0.34  # Propositional unsat checks           : 0
% 0.15/0.34  #    Propositional check models        : 0
% 0.15/0.34  #    Propositional check unsatisfiable : 0
% 0.15/0.34  #    Propositional clauses             : 0
% 0.15/0.34  #    Propositional clauses after purity: 0
% 0.15/0.34  #    Propositional unsat core size     : 0
% 0.15/0.34  #    Propositional preprocessing time  : 0.000
% 0.15/0.34  #    Propositional encoding time       : 0.000
% 0.15/0.34  #    Propositional solver time         : 0.000
% 0.15/0.34  #    Success case prop preproc time    : 0.000
% 0.15/0.34  #    Success case prop encoding time   : 0.000
% 0.15/0.34  #    Success case prop solver time     : 0.000
% 0.15/0.34  # Current number of processed clauses  : 77
% 0.15/0.34  #    Positive orientable unit clauses  : 12
% 0.15/0.34  #    Positive unorientable unit clauses: 1
% 0.15/0.34  #    Negative unit clauses             : 5
% 0.15/0.34  #    Non-unit-clauses                  : 59
% 0.15/0.34  # Current number of unprocessed clauses: 143
% 0.15/0.34  # ...number of literals in the above   : 620
% 0.15/0.34  # Current number of archived formulas  : 0
% 0.15/0.34  # Current number of archived clauses   : 32
% 0.15/0.34  # Clause-clause subsumption calls (NU) : 721
% 0.15/0.34  # Rec. Clause-clause subsumption calls : 246
% 0.15/0.34  # Non-unit clause-clause subsumptions  : 47
% 0.15/0.34  # Unit Clause-clause subsumption calls : 26
% 0.15/0.34  # Rewrite failures with RHS unbound    : 3
% 0.15/0.34  # BW rewrite match attempts            : 20
% 0.15/0.34  # BW rewrite match successes           : 7
% 0.15/0.34  # Condensation attempts                : 0
% 0.15/0.34  # Condensation successes               : 0
% 0.15/0.34  # Termbank termtop insertions          : 6185
% 0.15/0.34  
% 0.15/0.34  # -------------------------------------------------
% 0.15/0.34  # User time                : 0.036 s
% 0.15/0.34  # System time              : 0.006 s
% 0.15/0.34  # Total time               : 0.042 s
% 0.15/0.34  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
