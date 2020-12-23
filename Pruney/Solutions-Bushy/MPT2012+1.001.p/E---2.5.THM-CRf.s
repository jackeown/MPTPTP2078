%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2012+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:07 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   34 (  83 expanded)
%              Number of clauses        :   21 (  33 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 220 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_waybel_9,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = g1_orders_2(u1_struct_0(k3_waybel_9(X1)),u1_orders_2(k3_waybel_9(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_9)).

fof(dt_k3_waybel_9,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v6_waybel_0(k3_waybel_9(X1),X1)
        & l1_waybel_0(k3_waybel_9(X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_9)).

fof(d6_waybel_9,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v6_waybel_0(X2,X1)
            & l1_waybel_0(X2,X1) )
         => ( X2 = k3_waybel_9(X1)
          <=> ( u1_struct_0(X2) = u1_struct_0(X1)
              & u1_orders_2(X2) = k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))
              & u1_waybel_0(X1,X2) = k3_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_9)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(d5_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = g1_orders_2(u1_struct_0(k3_waybel_9(X1)),u1_orders_2(k3_waybel_9(X1))) ) ),
    inference(assume_negation,[status(cth)],[t11_waybel_9])).

fof(c_0_7,plain,(
    ! [X7] :
      ( ( v6_waybel_0(k3_waybel_9(X7),X7)
        | ~ l1_orders_2(X7) )
      & ( l1_waybel_0(k3_waybel_9(X7),X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_waybel_9])])])).

fof(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) != g1_orders_2(u1_struct_0(k3_waybel_9(esk1_0)),u1_orders_2(k3_waybel_9(esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ( u1_struct_0(X6) = u1_struct_0(X5)
        | X6 != k3_waybel_9(X5)
        | ~ v6_waybel_0(X6,X5)
        | ~ l1_waybel_0(X6,X5)
        | ~ l1_orders_2(X5) )
      & ( u1_orders_2(X6) = k3_relset_1(u1_struct_0(X5),u1_struct_0(X5),u1_orders_2(X5))
        | X6 != k3_waybel_9(X5)
        | ~ v6_waybel_0(X6,X5)
        | ~ l1_waybel_0(X6,X5)
        | ~ l1_orders_2(X5) )
      & ( u1_waybel_0(X5,X6) = k3_struct_0(X5)
        | X6 != k3_waybel_9(X5)
        | ~ v6_waybel_0(X6,X5)
        | ~ l1_waybel_0(X6,X5)
        | ~ l1_orders_2(X5) )
      & ( u1_struct_0(X6) != u1_struct_0(X5)
        | u1_orders_2(X6) != k3_relset_1(u1_struct_0(X5),u1_struct_0(X5),u1_orders_2(X5))
        | u1_waybel_0(X5,X6) != k3_struct_0(X5)
        | X6 = k3_waybel_9(X5)
        | ~ v6_waybel_0(X6,X5)
        | ~ l1_waybel_0(X6,X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_waybel_9])])])])).

cnf(c_0_10,plain,
    ( l1_waybel_0(k3_waybel_9(X1),X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v6_waybel_0(k3_waybel_9(X1),X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X8] :
      ( ( v1_orders_2(k7_lattice3(X8))
        | ~ l1_orders_2(X8) )
      & ( l1_orders_2(k7_lattice3(X8))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

cnf(c_0_14,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | X1 != k3_waybel_9(X2)
    | ~ v6_waybel_0(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_waybel_0(k3_waybel_9(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v6_waybel_0(k3_waybel_9(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

fof(c_0_17,plain,(
    ! [X3] :
      ( ~ l1_orders_2(X3)
      | ~ v1_orders_2(X3)
      | X3 = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_18,plain,
    ( v1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X4] :
      ( ~ l1_orders_2(X4)
      | k7_lattice3(X4) = g1_orders_2(u1_struct_0(X4),k3_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).

cnf(c_0_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) != g1_orders_2(u1_struct_0(k3_waybel_9(esk1_0)),u1_orders_2(k3_waybel_9(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(k3_waybel_9(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_11])])).

cnf(c_0_23,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_26,plain,
    ( k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( u1_orders_2(X1) = k3_relset_1(u1_struct_0(X2),u1_struct_0(X2),u1_orders_2(X2))
    | X1 != k3_waybel_9(X2)
    | ~ v6_waybel_0(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k3_waybel_9(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_30,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = u1_orders_2(k3_waybel_9(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_16]),c_0_11])])).

cnf(c_0_32,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k3_waybel_9(esk1_0))) != k7_lattice3(esk1_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),
    [proof]).

%------------------------------------------------------------------------------
