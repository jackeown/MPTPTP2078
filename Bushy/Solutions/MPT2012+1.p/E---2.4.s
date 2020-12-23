%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_9__t11_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:08 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  58 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 188 expanded)
%              Number of equality atoms :   33 (  59 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_waybel_9,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = g1_orders_2(u1_struct_0(k3_waybel_9(X1)),u1_orders_2(k3_waybel_9(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t11_waybel_9.p',t11_waybel_9)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t11_waybel_9.p',abstractness_v1_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t11_waybel_9.p',d6_waybel_9)).

fof(dt_k3_waybel_9,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v6_waybel_0(k3_waybel_9(X1),X1)
        & l1_waybel_0(k3_waybel_9(X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t11_waybel_9.p',dt_k3_waybel_9)).

fof(d5_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t11_waybel_9.p',d5_lattice3)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t11_waybel_9.p',dt_k7_lattice3)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = g1_orders_2(u1_struct_0(k3_waybel_9(X1)),u1_orders_2(k3_waybel_9(X1))) ) ),
    inference(assume_negation,[status(cth)],[t11_waybel_9])).

fof(c_0_7,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) != g1_orders_2(u1_struct_0(k3_waybel_9(esk1_0)),u1_orders_2(k3_waybel_9(esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | ~ v1_orders_2(X10)
      | X10 = g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_9,plain,(
    ! [X16,X17] :
      ( ( u1_struct_0(X17) = u1_struct_0(X16)
        | X17 != k3_waybel_9(X16)
        | ~ v6_waybel_0(X17,X16)
        | ~ l1_waybel_0(X17,X16)
        | ~ l1_orders_2(X16) )
      & ( u1_orders_2(X17) = k3_relset_1(u1_struct_0(X16),u1_struct_0(X16),u1_orders_2(X16))
        | X17 != k3_waybel_9(X16)
        | ~ v6_waybel_0(X17,X16)
        | ~ l1_waybel_0(X17,X16)
        | ~ l1_orders_2(X16) )
      & ( u1_waybel_0(X16,X17) = k3_struct_0(X16)
        | X17 != k3_waybel_9(X16)
        | ~ v6_waybel_0(X17,X16)
        | ~ l1_waybel_0(X17,X16)
        | ~ l1_orders_2(X16) )
      & ( u1_struct_0(X17) != u1_struct_0(X16)
        | u1_orders_2(X17) != k3_relset_1(u1_struct_0(X16),u1_struct_0(X16),u1_orders_2(X16))
        | u1_waybel_0(X16,X17) != k3_struct_0(X16)
        | X17 = k3_waybel_9(X16)
        | ~ v6_waybel_0(X17,X16)
        | ~ l1_waybel_0(X17,X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_waybel_9])])])])).

fof(c_0_10,plain,(
    ! [X28] :
      ( ( v6_waybel_0(k3_waybel_9(X28),X28)
        | ~ l1_orders_2(X28) )
      & ( l1_waybel_0(k3_waybel_9(X28),X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_waybel_9])])])).

cnf(c_0_11,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) != g1_orders_2(u1_struct_0(k3_waybel_9(esk1_0)),u1_orders_2(k3_waybel_9(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | X1 != k3_waybel_9(X2)
    | ~ v6_waybel_0(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v6_waybel_0(k3_waybel_9(X1),X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( l1_waybel_0(k3_waybel_9(X1),X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | k7_lattice3(X15) = g1_orders_2(u1_struct_0(X15),k3_relset_1(u1_struct_0(X15),u1_struct_0(X15),u1_orders_2(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).

cnf(c_0_17,plain,
    ( u1_orders_2(X1) = k3_relset_1(u1_struct_0(X2),u1_struct_0(X2),u1_orders_2(X2))
    | X1 != k3_waybel_9(X2)
    | ~ v6_waybel_0(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k3_waybel_9(esk1_0)),u1_orders_2(k3_waybel_9(esk1_0))) != k7_lattice3(esk1_0)
    | ~ v1_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( u1_struct_0(k3_waybel_9(X1)) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)) = u1_orders_2(k3_waybel_9(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k3_waybel_9(esk1_0))) != k7_lattice3(esk1_0)
    | ~ v1_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_24,plain,
    ( g1_orders_2(u1_struct_0(X1),u1_orders_2(k3_waybel_9(X1))) = k7_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X32] :
      ( ( v1_orders_2(k7_lattice3(X32))
        | ~ l1_orders_2(X32) )
      & ( l1_orders_2(k7_lattice3(X32))
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_orders_2(k7_lattice3(esk1_0))
    | ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20])])).

cnf(c_0_27,plain,
    ( v1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( ~ l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_20])])).

cnf(c_0_29,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
