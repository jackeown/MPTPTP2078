%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1528+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:20 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   24 (  44 expanded)
%              Number of clauses        :   14 (  19 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 152 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r2_lattice3(X1,k1_xboole_0,X2)
              & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_yellow_0])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_hidden(X8,X6)
        | r1_orders_2(X5,X7,X8)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X7,esk1_3(X5,X6,X7))
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_7,negated_conjecture,
    ( l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ( ~ r2_lattice3(esk3_0,k1_xboole_0,esk4_0)
      | ~ r1_lattice3(esk3_0,k1_xboole_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | ~ v1_xboole_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X11)
        | r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_3(X10,X11,X12),u1_struct_0(X10))
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r2_hidden(esk2_3(X10,X11,X12),X11)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk2_3(X10,X11,X12),X12)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,X2),X1)
    | r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,k1_xboole_0,esk4_0)
    | ~ r1_lattice3(esk3_0,k1_xboole_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,esk4_0),X1)
    | r1_lattice3(esk3_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | r2_hidden(esk2_3(esk3_0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,k1_xboole_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk4_0)
    | r2_hidden(esk2_3(esk3_0,X1,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19]),
    [proof]).

%------------------------------------------------------------------------------
