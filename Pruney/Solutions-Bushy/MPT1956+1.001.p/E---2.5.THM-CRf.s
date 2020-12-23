%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1956+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:04 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 125 expanded)
%              Number of clauses        :   25 (  44 expanded)
%              Number of leaves         :    7 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 799 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ( r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
            & r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

fof(t35_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r2_yellow_0(X1,X2)
            & r2_yellow_0(X1,X3) )
         => r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).

fof(t17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(t34_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r1_yellow_0(X1,X2)
            & r1_yellow_0(X1,X3) )
         => r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => ( r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
              & r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_waybel_7])).

fof(c_0_8,plain,(
    ! [X15,X16,X17] :
      ( ~ l1_orders_2(X15)
      | ~ r1_tarski(X16,X17)
      | ~ r2_yellow_0(X15,X16)
      | ~ r2_yellow_0(X15,X17)
      | r1_orders_2(X15,k2_yellow_0(X15,X17),k2_yellow_0(X15,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_yellow_0])])])).

fof(c_0_9,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_lattice3(esk1_0)
    & v2_lattice3(esk1_0)
    & v3_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & ( ~ r3_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk3_0))
      | ~ r1_orders_2(esk1_0,k2_yellow_0(esk1_0,esk3_0),k2_yellow_0(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_10,plain,
    ( r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X10,X11] :
      ( ( r1_yellow_0(X10,X11)
        | v2_struct_0(X10)
        | ~ v5_orders_2(X10)
        | ~ v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_yellow_0(X10,X11)
        | v2_struct_0(X10)
        | ~ v5_orders_2(X10)
        | ~ v3_lattice3(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).

fof(c_0_13,plain,(
    ! [X4] :
      ( ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v2_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14] :
      ( ~ l1_orders_2(X12)
      | ~ r1_tarski(X13,X14)
      | ~ r1_yellow_0(X12,X13)
      | ~ r1_yellow_0(X12,X14)
      | r1_orders_2(X12,k1_yellow_0(X12,X13),k1_yellow_0(X12,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_orders_2(X1,k2_yellow_0(X1,esk3_0),k2_yellow_0(X1,esk2_0))
    | ~ r2_yellow_0(X1,esk3_0)
    | ~ r2_yellow_0(X1,esk2_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(X1,k2_yellow_0(X1,esk3_0),k2_yellow_0(X1,esk2_0))
    | v2_struct_0(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v3_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(X1,k1_yellow_0(X1,esk2_0),k1_yellow_0(X1,esk3_0))
    | ~ r1_yellow_0(X1,esk3_0)
    | ~ r1_yellow_0(X1,esk2_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_26,plain,
    ( r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk3_0))
    | ~ r1_orders_2(esk1_0,k2_yellow_0(esk1_0,esk3_0),k2_yellow_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk1_0,k2_yellow_0(esk1_0,esk3_0),k2_yellow_0(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_19])]),c_0_24])).

fof(c_0_29,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r3_orders_2(X7,X8,X9)
        | r1_orders_2(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v3_orders_2(X7)
        | ~ l1_orders_2(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) )
      & ( ~ r1_orders_2(X7,X8,X9)
        | r3_orders_2(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v3_orders_2(X7)
        | ~ l1_orders_2(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(X1,k1_yellow_0(X1,esk2_0),k1_yellow_0(X1,esk3_0))
    | v2_struct_0(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_32,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_23]),c_0_19])]),c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_35,plain,(
    ! [X5,X6] :
      ( ~ l1_orders_2(X5)
      | m1_subset_1(k1_yellow_0(X5,X6),u1_struct_0(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(k1_yellow_0(esk1_0,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k1_yellow_0(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_19])]),c_0_24])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(k1_yellow_0(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_19])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_19])]),
    [proof]).

%------------------------------------------------------------------------------
