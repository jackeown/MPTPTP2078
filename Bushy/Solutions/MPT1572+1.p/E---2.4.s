%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t50_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:44 EDT 2019

% Result     : Theorem 151.26s
% Output     : CNFRefutation 151.26s
% Verified   : 
% Statistics : Number of formulae       :   88 (17972319 expanded)
%              Number of clauses        :   79 (6217479 expanded)
%              Number of leaves         :    4 (4323049 expanded)
%              Depth                    :   47
%              Number of atoms          :  436 (320338980 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   66 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( r1_yellow_0(X1,X2)
           => r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
          & ( r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
           => r1_yellow_0(X1,X2) )
          & ( r2_yellow_0(X1,X2)
           => r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
          & ( r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
           => r2_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t50_yellow_0.p',t50_yellow_0)).

fof(t48_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) )
            & r2_yellow_0(X1,X2) )
         => r2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t50_yellow_0.p',t48_yellow_0)).

fof(t5_yellow_0,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t50_yellow_0.p',t5_yellow_0)).

fof(t46_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                <=> r2_lattice3(X1,X3,X4) ) )
            & r1_yellow_0(X1,X2) )
         => r1_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t50_yellow_0.p',t46_yellow_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( r1_yellow_0(X1,X2)
             => r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
            & ( r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
             => r1_yellow_0(X1,X2) )
            & ( r2_yellow_0(X1,X2)
             => r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
            & ( r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
             => r2_yellow_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_yellow_0])).

fof(c_0_5,plain,(
    ! [X26,X27,X28] :
      ( ( m1_subset_1(esk7_3(X26,X27,X28),u1_struct_0(X26))
        | ~ r2_yellow_0(X26,X27)
        | r2_yellow_0(X26,X28)
        | v2_struct_0(X26)
        | ~ l1_orders_2(X26) )
      & ( ~ r1_lattice3(X26,X27,esk7_3(X26,X27,X28))
        | ~ r1_lattice3(X26,X28,esk7_3(X26,X27,X28))
        | ~ r2_yellow_0(X26,X27)
        | r2_yellow_0(X26,X28)
        | v2_struct_0(X26)
        | ~ l1_orders_2(X26) )
      & ( r1_lattice3(X26,X27,esk7_3(X26,X27,X28))
        | r1_lattice3(X26,X28,esk7_3(X26,X27,X28))
        | ~ r2_yellow_0(X26,X27)
        | r2_yellow_0(X26,X28)
        | v2_struct_0(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_yellow_0])])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r2_yellow_0(esk1_0,esk2_0)
      | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r1_yellow_0(esk1_0,esk2_0) )
    & ( ~ r2_yellow_0(esk1_0,esk2_0)
      | r2_yellow_0(esk1_0,esk2_0)
      | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r1_yellow_0(esk1_0,esk2_0) )
    & ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r1_yellow_0(esk1_0,esk2_0) )
    & ( ~ r2_yellow_0(esk1_0,esk2_0)
      | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r1_yellow_0(esk1_0,esk2_0) )
    & ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r2_yellow_0(esk1_0,esk2_0)
      | ~ r1_yellow_0(esk1_0,esk2_0)
      | r1_yellow_0(esk1_0,esk2_0) )
    & ( ~ r2_yellow_0(esk1_0,esk2_0)
      | r2_yellow_0(esk1_0,esk2_0)
      | ~ r1_yellow_0(esk1_0,esk2_0)
      | r1_yellow_0(esk1_0,esk2_0) )
    & ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r1_yellow_0(esk1_0,esk2_0)
      | r1_yellow_0(esk1_0,esk2_0) )
    & ( ~ r2_yellow_0(esk1_0,esk2_0)
      | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r1_yellow_0(esk1_0,esk2_0)
      | r1_yellow_0(esk1_0,esk2_0) )
    & ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r2_yellow_0(esk1_0,esk2_0)
      | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) )
    & ( ~ r2_yellow_0(esk1_0,esk2_0)
      | r2_yellow_0(esk1_0,esk2_0)
      | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) )
    & ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) )
    & ( ~ r2_yellow_0(esk1_0,esk2_0)
      | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) )
    & ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | r2_yellow_0(esk1_0,esk2_0)
      | ~ r1_yellow_0(esk1_0,esk2_0)
      | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) )
    & ( ~ r2_yellow_0(esk1_0,esk2_0)
      | r2_yellow_0(esk1_0,esk2_0)
      | ~ r1_yellow_0(esk1_0,esk2_0)
      | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) )
    & ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r1_yellow_0(esk1_0,esk2_0)
      | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) )
    & ( ~ r2_yellow_0(esk1_0,esk2_0)
      | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
      | ~ r1_yellow_0(esk1_0,esk2_0)
      | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

fof(c_0_7,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r2_lattice3(X30,X31,X32)
        | r2_lattice3(X30,k3_xboole_0(X31,u1_struct_0(X30)),X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ l1_orders_2(X30) )
      & ( ~ r2_lattice3(X30,k3_xboole_0(X31,u1_struct_0(X30)),X32)
        | r2_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ l1_orders_2(X30) )
      & ( ~ r1_lattice3(X30,X31,X32)
        | r1_lattice3(X30,k3_xboole_0(X31,u1_struct_0(X30)),X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ l1_orders_2(X30) )
      & ( ~ r1_lattice3(X30,k3_xboole_0(X31,u1_struct_0(X30)),X32)
        | r1_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_yellow_0])])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r1_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X1)
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_14,plain,
    ( r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r1_lattice3(X1,X3,esk7_3(X1,X2,X3))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X2)
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0)
    | ~ r1_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_10])]),c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r1_lattice3(esk1_0,X1,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X1)
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r1_lattice3(esk1_0,X1,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X1)
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_18,plain,
    ( r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X3,esk7_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk2_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(ef,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X22,X23,X24] :
      ( ( m1_subset_1(esk6_3(X22,X23,X24),u1_struct_0(X22))
        | ~ r1_yellow_0(X22,X23)
        | r1_yellow_0(X22,X24)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r2_lattice3(X22,X23,esk6_3(X22,X23,X24))
        | ~ r2_lattice3(X22,X24,esk6_3(X22,X23,X24))
        | ~ r1_yellow_0(X22,X23)
        | r1_yellow_0(X22,X24)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_lattice3(X22,X23,esk6_3(X22,X23,X24))
        | r2_lattice3(X22,X24,esk6_3(X22,X23,X24))
        | ~ r1_yellow_0(X22,X23)
        | r1_yellow_0(X22,X24)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_yellow_0])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X2)
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0)
    | ~ r1_lattice3(esk1_0,X1,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_10])]),c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0)
    | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_10])]),c_0_11]),c_0_9])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_23])).

cnf(c_0_26,plain,
    ( r2_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_10])]),c_0_11])).

cnf(c_0_28,plain,
    ( r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r2_lattice3(X1,X3,esk6_3(X1,X2,X3))
    | r1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2))
    | r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X2)
    | ~ r2_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_10])]),c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_lattice3(esk1_0,X1,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_10])]),c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_lattice3(esk1_0,X1,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,plain,
    ( r1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X3,esk6_3(X1,X2,X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk2_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2))
    | r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X2)
    | ~ r2_lattice3(esk1_0,X1,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_10])]),c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,esk2_0)
    | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_10])]),c_0_11]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_36])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,X1)
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_37]),c_0_10])]),c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk7_3(esk1_0,esk2_0,X2))
    | r2_yellow_0(esk1_0,X2)
    | r1_yellow_0(esk1_0,esk2_0)
    | ~ r1_lattice3(esk1_0,X1,esk7_3(esk1_0,esk2_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_38]),c_0_10])]),c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,X1))
    | r1_lattice3(esk1_0,X1,esk7_3(esk1_0,esk2_0,X1))
    | r2_yellow_0(esk1_0,X1)
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_37]),c_0_10])]),c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk7_3(esk1_0,esk2_0,X1))
    | r1_lattice3(esk1_0,X1,esk7_3(esk1_0,esk2_0,X1))
    | r2_yellow_0(esk1_0,X1)
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk7_3(esk1_0,esk2_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))))
    | r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(ef,[status(thm)],[c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0)
    | ~ r2_yellow_0(esk1_0,esk2_0)
    | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk7_3(esk1_0,esk2_0,X2))
    | r2_yellow_0(esk1_0,X2)
    | r1_yellow_0(esk1_0,esk2_0)
    | ~ r1_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk7_3(esk1_0,esk2_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_38]),c_0_10])]),c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0)
    | ~ r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_42]),c_0_10])]),c_0_11]),c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0)
    | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_42]),c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1),u1_struct_0(esk1_0))
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_48]),c_0_10])]),c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2))
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X2)
    | ~ r2_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_49]),c_0_10])]),c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_lattice3(esk1_0,X1,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_48]),c_0_10])]),c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_lattice3(esk1_0,X1,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk2_0))
    | r1_yellow_0(esk1_0,esk2_0) ),
    inference(ef,[status(thm)],[c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2))
    | r1_yellow_0(esk1_0,esk2_0)
    | r1_yellow_0(esk1_0,X2)
    | ~ r2_lattice3(esk1_0,X1,esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_49]),c_0_10])]),c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk2_0)
    | ~ r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk6_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_53]),c_0_10])]),c_0_11]),c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | r1_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_56]),c_0_10])]),c_0_11])).

cnf(c_0_58,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk6_3(esk1_0,esk2_0,X2))
    | r1_yellow_0(esk1_0,X2)
    | ~ r2_lattice3(esk1_0,X1,esk6_3(esk1_0,esk2_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_57]),c_0_10])]),c_0_11])).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk6_3(esk1_0,esk2_0,X1))
    | r2_lattice3(esk1_0,X1,esk6_3(esk1_0,esk2_0,X1))
    | r1_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_56]),c_0_10])]),c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk6_3(esk1_0,esk2_0,X1))
    | r2_lattice3(esk1_0,X1,esk6_3(esk1_0,esk2_0,X1))
    | r1_yellow_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( r2_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk6_3(esk1_0,esk2_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))))
    | r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(ef,[status(thm)],[c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_yellow_0(esk1_0,esk2_0)
    | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_63,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk6_3(esk1_0,esk2_0,X2))
    | r1_yellow_0(esk1_0,X2)
    | ~ r2_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk6_3(esk1_0,esk2_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_57]),c_0_10])]),c_0_11])).

cnf(c_0_64,negated_conjecture,
    ( r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | ~ r2_lattice3(esk1_0,esk2_0,esk6_3(esk1_0,esk2_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_61]),c_0_56]),c_0_10])]),c_0_11])).

cnf(c_0_65,negated_conjecture,
    ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_56])])).

cnf(c_0_66,negated_conjecture,
    ( r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_61]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_67]),c_0_10])]),c_0_11])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X2)
    | ~ r1_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_68]),c_0_10])]),c_0_11])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r1_lattice3(esk1_0,X1,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_67]),c_0_10])]),c_0_11])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r1_lattice3(esk1_0,X1,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X1))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk2_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(ef,[status(thm)],[c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2))
    | r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,X2)
    | ~ r1_lattice3(esk1_0,X1,esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_68]),c_0_10])]),c_0_11])).

cnf(c_0_74,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk7_3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_72]),c_0_10])]),c_0_11]),c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_72]),c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_yellow_0(esk1_0,esk2_0)
    | ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | ~ r1_yellow_0(esk1_0,esk2_0)
    | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_75]),c_0_10])]),c_0_11])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | ~ r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_56])])).

cnf(c_0_79,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk7_3(esk1_0,esk2_0,X2))
    | r2_yellow_0(esk1_0,X2)
    | ~ r1_lattice3(esk1_0,X1,esk7_3(esk1_0,esk2_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_77]),c_0_10])]),c_0_11])).

cnf(c_0_80,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,X1))
    | r1_lattice3(esk1_0,X1,esk7_3(esk1_0,esk2_0,X1))
    | r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_75]),c_0_10])]),c_0_11])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))
    | ~ r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_66])])).

cnf(c_0_82,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk7_3(esk1_0,esk2_0,X1))
    | r1_lattice3(esk1_0,X1,esk7_3(esk1_0,esk2_0,X1))
    | r2_yellow_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_yellow_0(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_75])])).

cnf(c_0_84,negated_conjecture,
    ( r1_lattice3(esk1_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)),esk7_3(esk1_0,esk2_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_82]),c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk7_3(esk1_0,esk2_0,X2))
    | r2_yellow_0(esk1_0,X2)
    | ~ r1_lattice3(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0)),esk7_3(esk1_0,esk2_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_77]),c_0_10])]),c_0_11])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,k3_xboole_0(esk2_0,u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_84]),c_0_75]),c_0_10])]),c_0_83]),c_0_11])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_84]),c_0_83]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
