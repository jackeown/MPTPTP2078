%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1564+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 (2371 expanded)
%              Number of clauses        :   49 ( 865 expanded)
%              Number of leaves         :    9 ( 571 expanded)
%              Depth                    :   19
%              Number of atoms          :  280 (11938 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(d4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_yellow_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & r1_lattice3(X1,u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

fof(t16_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t15_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & l1_orders_2(X1) )
       => ( r1_yellow_0(X1,k1_xboole_0)
          & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t42_yellow_0])).

fof(c_0_10,plain,(
    ! [X5,X7] :
      ( ( m1_subset_1(esk1_1(X5),u1_struct_0(X5))
        | ~ v1_yellow_0(X5)
        | ~ l1_orders_2(X5) )
      & ( r1_lattice3(X5,u1_struct_0(X5),esk1_1(X5))
        | ~ v1_yellow_0(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ r1_lattice3(X5,u1_struct_0(X5),X7)
        | v1_yellow_0(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_yellow_0])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v5_orders_2(esk7_0)
    & v1_yellow_0(esk7_0)
    & l1_orders_2(esk7_0)
    & ( ~ r1_yellow_0(esk7_0,k1_xboole_0)
      | ~ r2_yellow_0(esk7_0,u1_struct_0(esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X22,X23,X25,X26,X27] :
      ( ( m1_subset_1(esk5_2(X22,X23),u1_struct_0(X22))
        | ~ r2_yellow_0(X22,X23)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_lattice3(X22,X23,esk5_2(X22,X23))
        | ~ r2_yellow_0(X22,X23)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r1_lattice3(X22,X23,X25)
        | r1_orders_2(X22,X25,esk5_2(X22,X23))
        | ~ r2_yellow_0(X22,X23)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk6_3(X22,X26,X27),u1_struct_0(X22))
        | ~ m1_subset_1(X27,u1_struct_0(X22))
        | ~ r1_lattice3(X22,X26,X27)
        | r2_yellow_0(X22,X26)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_lattice3(X22,X26,esk6_3(X22,X26,X27))
        | ~ m1_subset_1(X27,u1_struct_0(X22))
        | ~ r1_lattice3(X22,X26,X27)
        | r2_yellow_0(X22,X26)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,esk6_3(X22,X26,X27),X27)
        | ~ m1_subset_1(X27,u1_struct_0(X22))
        | ~ r1_lattice3(X22,X26,X27)
        | r2_yellow_0(X22,X26)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_0])])])])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk1_1(X1),u1_struct_0(X1))
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_yellow_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_17,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_18,plain,
    ( r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk1_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_20,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r1_lattice3(X1,u1_struct_0(X1),esk1_1(X1))
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_22,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( m1_subset_1(esk3_2(X15,X16),u1_struct_0(X15))
        | ~ r1_yellow_0(X15,X16)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r2_lattice3(X15,X16,esk3_2(X15,X16))
        | ~ r1_yellow_0(X15,X16)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_lattice3(X15,X16,X18)
        | r1_orders_2(X15,esk3_2(X15,X16),X18)
        | ~ r1_yellow_0(X15,X16)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk4_3(X15,X19,X20),u1_struct_0(X15))
        | ~ m1_subset_1(X20,u1_struct_0(X15))
        | ~ r2_lattice3(X15,X19,X20)
        | r1_yellow_0(X15,X19)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r2_lattice3(X15,X19,esk4_3(X15,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X15))
        | ~ r2_lattice3(X15,X19,X20)
        | r1_yellow_0(X15,X19)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,X20,esk4_3(X15,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X15))
        | ~ r2_lattice3(X15,X19,X20)
        | r1_yellow_0(X15,X19)
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

fof(c_0_23,plain,(
    ! [X31,X32] :
      ( ( r2_lattice3(X31,k1_xboole_0,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( r1_lattice3(X31,k1_xboole_0,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_25,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r1_lattice3(X8,X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X8))
        | ~ r2_hidden(X11,X9)
        | r1_orders_2(X8,X10,X11)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk2_3(X8,X9,X10),u1_struct_0(X8))
        | r1_lattice3(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( r2_hidden(esk2_3(X8,X9,X10),X9)
        | r1_lattice3(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( ~ r1_orders_2(X8,X10,esk2_3(X8,X9,X10))
        | r1_lattice3(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_26,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r2_yellow_0(esk7_0,X1)
    | r1_lattice3(esk7_0,X1,esk6_3(esk7_0,X1,esk1_1(esk7_0)))
    | ~ r1_lattice3(esk7_0,X1,esk1_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( r1_lattice3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_15])])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r2_yellow_0(esk7_0,X1)
    | m1_subset_1(esk6_3(esk7_0,X1,esk1_1(esk7_0)),u1_struct_0(esk7_0))
    | ~ r1_lattice3(esk7_0,X1,esk1_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_20]),c_0_15])])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r2_hidden(esk1_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_yellow_0(esk7_0,k1_xboole_0)
    | ~ r2_yellow_0(esk7_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( r2_yellow_0(esk7_0,u1_struct_0(esk7_0))
    | r1_lattice3(esk7_0,u1_struct_0(esk7_0),esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r1_yellow_0(esk7_0,X1)
    | m1_subset_1(esk4_3(esk7_0,X1,esk1_1(esk7_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,X1,esk1_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_20]),c_0_15])])).

cnf(c_0_42,negated_conjecture,
    ( r2_lattice3(esk7_0,k1_xboole_0,esk1_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( r2_yellow_0(esk7_0,u1_struct_0(esk7_0))
    | m1_subset_1(esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,esk1_1(esk7_0))
    | ~ r2_hidden(esk1_1(esk7_0),X2)
    | ~ r1_lattice3(esk7_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_15])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_lattice3(esk7_0,u1_struct_0(esk7_0),esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0)))
    | ~ r1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_yellow_0(esk7_0,k1_xboole_0)
    | m1_subset_1(esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0)),u1_struct_0(esk7_0))
    | ~ r1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,esk1_1(esk7_0))
    | ~ r1_lattice3(esk7_0,u1_struct_0(esk7_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk7_0,u1_struct_0(esk7_0),esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0)))
    | m1_subset_1(esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_52,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk7_0,esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0)),esk1_1(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r2_yellow_0(esk7_0,u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_20]),c_0_30]),c_0_19]),c_0_15])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_54]),c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | r2_hidden(esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)))
    | ~ r2_hidden(esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)),X2)
    | ~ r1_lattice3(esk7_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_55]),c_0_15])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_56]),c_0_37])]),c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0)))
    | ~ r1_lattice3(esk7_0,u1_struct_0(esk7_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_60,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk7_0,esk1_1(esk7_0),esk4_3(esk7_0,k1_xboole_0,esk1_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_30]),c_0_19])])).

cnf(c_0_62,negated_conjecture,
    ( r1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_42]),c_0_20]),c_0_19]),c_0_15])])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattice3(esk7_0,u1_struct_0(esk7_0),esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_62])])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk7_0,esk6_3(esk7_0,u1_struct_0(esk7_0),esk1_1(esk7_0)),esk1_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_63]),c_0_64])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_yellow_0(esk7_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_62])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_65]),c_0_20]),c_0_30]),c_0_19]),c_0_15])]),c_0_66]),
    [proof]).

%------------------------------------------------------------------------------
