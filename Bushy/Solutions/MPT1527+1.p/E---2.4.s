%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t5_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:45 EDT 2019

% Result     : Theorem 152.70s
% Output     : CNFRefutation 152.70s
% Verified   : 
% Statistics : Number of formulae       :   84 (3896 expanded)
%              Number of clauses        :   67 (1541 expanded)
%              Number of leaves         :    8 ( 919 expanded)
%              Depth                    :   26
%              Number of atoms          :  360 (56184 expanded)
%              Number of equality atoms :    9 ( 336 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   67 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( ( r2_lattice3(X1,X2,X3)
             => r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3) )
            & ( r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
             => r2_lattice3(X1,X2,X3) )
            & ( r1_lattice3(X1,X2,X3)
             => r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3) )
            & ( r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
             => r1_lattice3(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',t5_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',dt_l1_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',d8_lattice3)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',t7_boole)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',d4_xboole_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',d9_lattice3)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ( ( r2_lattice3(X1,X2,X3)
               => r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3) )
              & ( r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
               => r2_lattice3(X1,X2,X3) )
              & ( r1_lattice3(X1,X2,X3)
               => r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3) )
              & ( r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
               => r1_lattice3(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_yellow_0])).

fof(c_0_9,plain,(
    ! [X40,X41] :
      ( ~ m1_subset_1(X40,X41)
      | v1_xboole_0(X41)
      | r2_hidden(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r1_lattice3(esk1_0,esk2_0,esk3_0)
      | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r2_lattice3(esk1_0,esk2_0,esk3_0) )
    & ( ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,esk2_0,esk3_0)
      | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r2_lattice3(esk1_0,esk2_0,esk3_0) )
    & ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r2_lattice3(esk1_0,esk2_0,esk3_0) )
    & ( ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r2_lattice3(esk1_0,esk2_0,esk3_0) )
    & ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r1_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
      | r2_lattice3(esk1_0,esk2_0,esk3_0) )
    & ( ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
      | r2_lattice3(esk1_0,esk2_0,esk3_0) )
    & ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
      | r2_lattice3(esk1_0,esk2_0,esk3_0) )
    & ( ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
      | r2_lattice3(esk1_0,esk2_0,esk3_0) )
    & ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r1_lattice3(esk1_0,esk2_0,esk3_0)
      | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) )
    & ( ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,esk2_0,esk3_0)
      | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) )
    & ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) )
    & ( ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) )
    & ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | r1_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) )
    & ( ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) )
    & ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) )
    & ( ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
      | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X47] :
      ( v2_struct_0(X47)
      | ~ l1_struct_0(X47)
      | ~ v1_xboole_0(u1_struct_0(X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_12,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X31] :
      ( ~ l1_orders_2(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_18,plain,(
    ! [X21,X22,X23,X24] :
      ( ( ~ r1_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r2_hidden(X24,X22)
        | r1_orders_2(X21,X23,X24)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk5_3(X21,X22,X23),u1_struct_0(X21))
        | r1_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( r2_hidden(esk5_3(X21,X22,X23),X22)
        | r1_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( ~ r1_orders_2(X21,X23,esk5_3(X21,X22,X23))
        | r1_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_19,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | ~ v1_xboole_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk4_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk4_3(X17,X18,X19),X17)
        | ~ r2_hidden(esk4_3(X17,X18,X19),X18)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk4_3(X17,X18,X19),X17)
        | r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk4_3(X17,X18,X19),X18)
        | r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

fof(c_0_27,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r2_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ r2_hidden(X29,X27)
        | r1_orders_2(X26,X29,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( m1_subset_1(esk6_3(X26,X27,X28),u1_struct_0(X26))
        | r2_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( r2_hidden(esk6_3(X26,X27,X28),X27)
        | r2_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( ~ r1_orders_2(X26,esk6_3(X26,X27,X28),X28)
        | r2_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk3_0)
    | m1_subset_1(esk5_3(esk1_0,X1,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_13]),c_0_22])])).

cnf(c_0_30,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk5_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk5_3(esk1_0,X2,esk3_0))
    | r1_lattice3(esk1_0,X2,esk3_0)
    | ~ r2_hidden(esk5_3(esk1_0,X2,esk3_0),X3)
    | ~ r1_lattice3(esk1_0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_22])])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk5_3(esk1_0,X1,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_22])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | r1_lattice3(esk1_0,X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_29]),c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk3_0)
    | m1_subset_1(esk6_3(esk1_0,X1,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_13]),c_0_22])])).

cnf(c_0_41,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk5_3(esk1_0,X1,esk3_0),X2)
    | ~ r1_lattice3(esk1_0,X2,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_13]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r1_lattice3(esk1_0,esk2_0,esk3_0)
    | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,esk3_0),k3_xboole_0(X2,u1_struct_0(esk1_0)))
    | r1_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk5_3(esk1_0,X1,esk3_0),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,esk3_0),X1)
    | r1_lattice3(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_13]),c_0_22])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,X1,esk3_0),X2)
    | r2_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk3_0),X3)
    | ~ r2_lattice3(esk1_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_22])])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,esk6_3(esk1_0,X1,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_13]),c_0_22])])).

cnf(c_0_48,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_0)
    | r1_lattice3(esk1_0,X1,esk3_0)
    | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk5_3(esk1_0,X1,esk3_0),k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,esk3_0),k3_xboole_0(X1,u1_struct_0(esk1_0)))
    | r1_lattice3(esk1_0,X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | r2_lattice3(esk1_0,X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_40]),c_0_32])).

cnf(c_0_51,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk3_0),X2)
    | ~ r2_lattice3(esk1_0,X2,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_13]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_0)
    | r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk3_0),k3_xboole_0(X2,u1_struct_0(esk1_0)))
    | r2_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk3_0),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk3_0),X1)
    | r2_lattice3(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_13]),c_0_22])])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0)
    | r2_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk3_0),k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk3_0),k3_xboole_0(X1,u1_struct_0(esk1_0)))
    | r2_lattice3(esk1_0,X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk5_3(esk1_0,X1,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,k3_xboole_0(X1,X2),esk3_0),X1)
    | r1_lattice3(esk1_0,k3_xboole_0(X1,X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,X1),esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk3_0)
    | r2_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk3_0),k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r1_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_70,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,k3_xboole_0(X1,X2),esk3_0),X1)
    | r2_lattice3(esk1_0,k3_xboole_0(X1,X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r1_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | r1_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | ~ r2_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_0)
    | r1_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk5_3(esk1_0,X1,esk3_0),k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_68])])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_49])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_73])])).

cnf(c_0_80,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk5_3(esk1_0,X1,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_78])])).

cnf(c_0_82,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_63])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
