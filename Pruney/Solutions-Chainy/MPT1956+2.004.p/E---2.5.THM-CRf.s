%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:21 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 178 expanded)
%              Number of clauses        :   33 (  65 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  240 (1135 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_7)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).

fof(t9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,X3,X4)
                 => r1_lattice3(X1,X2,X4) )
                & ( r2_lattice3(X1,X3,X4)
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(t35_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r2_yellow_0(X1,X2)
            & r2_yellow_0(X1,X3) )
         => r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v2_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_10,negated_conjecture,
    ( v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & v1_lattice3(esk2_0)
    & v2_lattice3(esk2_0)
    & v3_lattice3(esk2_0)
    & l1_orders_2(esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & ( ~ r3_orders_2(esk2_0,k1_yellow_0(esk2_0,esk3_0),k1_yellow_0(esk2_0,esk4_0))
      | ~ r1_orders_2(esk2_0,k2_yellow_0(esk2_0,esk4_0),k2_yellow_0(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r2_lattice3(X9,X10,X11)
        | X11 != k1_yellow_0(X9,X10)
        | ~ r1_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_lattice3(X9,X10,X12)
        | r1_orders_2(X9,X11,X12)
        | X11 != k1_yellow_0(X9,X10)
        | ~ r1_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))
        | ~ r2_lattice3(X9,X10,X11)
        | X11 = k1_yellow_0(X9,X10)
        | ~ r1_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( r2_lattice3(X9,X10,esk1_3(X9,X10,X11))
        | ~ r2_lattice3(X9,X10,X11)
        | X11 = k1_yellow_0(X9,X10)
        | ~ r1_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,X11,esk1_3(X9,X10,X11))
        | ~ r2_lattice3(X9,X10,X11)
        | X11 = k1_yellow_0(X9,X10)
        | ~ r1_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ~ l1_orders_2(X14)
      | m1_subset_1(k1_yellow_0(X14,X15),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( ( r1_yellow_0(X16,X17)
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v3_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_yellow_0(X16,X17)
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v3_lattice3(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).

cnf(c_0_14,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X21,X22,X23,X24] :
      ( ( ~ r1_lattice3(X21,X23,X24)
        | r1_lattice3(X21,X22,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r1_tarski(X22,X23)
        | ~ l1_orders_2(X21) )
      & ( ~ r2_lattice3(X21,X23,X24)
        | r2_lattice3(X21,X22,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r1_tarski(X22,X23)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).

cnf(c_0_18,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v3_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ~ l1_orders_2(X18)
      | ~ r1_tarski(X19,X20)
      | ~ r2_yellow_0(X18,X19)
      | ~ r2_yellow_0(X18,X20)
      | r1_orders_2(X18,k2_yellow_0(X18,X20),k2_yellow_0(X18,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_yellow_0])])])).

cnf(c_0_25,plain,
    ( r2_lattice3(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r1_yellow_0(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_16])]),c_0_23])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_30,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r3_orders_2(X5,X6,X7)
        | r1_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) )
      & ( ~ r1_orders_2(X5,X6,X7)
        | r3_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_31,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ r1_tarski(X2,X4)
    | ~ r2_lattice3(X1,X4,k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,k1_yellow_0(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16])])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(X1,k2_yellow_0(X1,esk4_0),k2_yellow_0(X1,esk3_0))
    | ~ r2_yellow_0(X1,esk4_0)
    | ~ r2_yellow_0(X1,esk3_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,k1_yellow_0(esk2_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_16])])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(X1,k2_yellow_0(X1,esk4_0),k2_yellow_0(X1,esk3_0))
    | v2_struct_0(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_35])).

cnf(c_0_40,plain,
    ( r3_orders_2(X1,X2,k1_yellow_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,k1_yellow_0(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_19])).

cnf(c_0_41,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,k1_yellow_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( ~ r3_orders_2(esk2_0,k1_yellow_0(esk2_0,esk3_0),k1_yellow_0(esk2_0,esk4_0))
    | ~ r1_orders_2(esk2_0,k2_yellow_0(esk2_0,esk4_0),k2_yellow_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk2_0,k2_yellow_0(esk2_0,esk4_0),k2_yellow_0(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_21]),c_0_22]),c_0_16])]),c_0_23])).

cnf(c_0_45,plain,
    ( r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk2_0,k1_yellow_0(esk2_0,esk3_0),k1_yellow_0(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_27]),c_0_16])])).

cnf(c_0_47,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( ~ r3_orders_2(esk2_0,k1_yellow_0(esk2_0,esk3_0),k1_yellow_0(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_16]),c_0_47])]),c_0_48]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:50:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.18/0.37  # and selection function SelectNewComplexAHP.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.027 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(t3_waybel_7, conjecture, ![X1]:(((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))&r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_waybel_7)).
% 0.18/0.37  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.18/0.37  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.18/0.37  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.18/0.37  fof(t17_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(r1_yellow_0(X1,X2)&r2_yellow_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow_0)).
% 0.18/0.37  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 0.18/0.37  fof(t35_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(((r1_tarski(X2,X3)&r2_yellow_0(X1,X2))&r2_yellow_0(X1,X3))=>r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_yellow_0)).
% 0.18/0.37  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.18/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))&r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t3_waybel_7])).
% 0.18/0.37  fof(c_0_9, plain, ![X8]:(~l1_orders_2(X8)|(~v1_lattice3(X8)|~v2_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.18/0.37  fof(c_0_10, negated_conjecture, (((((((v3_orders_2(esk2_0)&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&v2_lattice3(esk2_0))&v3_lattice3(esk2_0))&l1_orders_2(esk2_0))&(r1_tarski(esk3_0,esk4_0)&(~r3_orders_2(esk2_0,k1_yellow_0(esk2_0,esk3_0),k1_yellow_0(esk2_0,esk4_0))|~r1_orders_2(esk2_0,k2_yellow_0(esk2_0,esk4_0),k2_yellow_0(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.18/0.37  fof(c_0_11, plain, ![X9, X10, X11, X12]:(((r2_lattice3(X9,X10,X11)|X11!=k1_yellow_0(X9,X10)|~r1_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_lattice3(X9,X10,X12)|r1_orders_2(X9,X11,X12))|X11!=k1_yellow_0(X9,X10)|~r1_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9)))&((m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))|~r2_lattice3(X9,X10,X11)|X11=k1_yellow_0(X9,X10)|~r1_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((r2_lattice3(X9,X10,esk1_3(X9,X10,X11))|~r2_lattice3(X9,X10,X11)|X11=k1_yellow_0(X9,X10)|~r1_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&(~r1_orders_2(X9,X11,esk1_3(X9,X10,X11))|~r2_lattice3(X9,X10,X11)|X11=k1_yellow_0(X9,X10)|~r1_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.18/0.37  fof(c_0_12, plain, ![X14, X15]:(~l1_orders_2(X14)|m1_subset_1(k1_yellow_0(X14,X15),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.18/0.37  fof(c_0_13, plain, ![X16, X17]:((r1_yellow_0(X16,X17)|(v2_struct_0(X16)|~v5_orders_2(X16)|~v3_lattice3(X16)|~l1_orders_2(X16)))&(r2_yellow_0(X16,X17)|(v2_struct_0(X16)|~v5_orders_2(X16)|~v3_lattice3(X16)|~l1_orders_2(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).
% 0.18/0.37  cnf(c_0_14, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_15, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  fof(c_0_17, plain, ![X21, X22, X23, X24]:((~r1_lattice3(X21,X23,X24)|r1_lattice3(X21,X22,X24)|~m1_subset_1(X24,u1_struct_0(X21))|~r1_tarski(X22,X23)|~l1_orders_2(X21))&(~r2_lattice3(X21,X23,X24)|r2_lattice3(X21,X22,X24)|~m1_subset_1(X24,u1_struct_0(X21))|~r1_tarski(X22,X23)|~l1_orders_2(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 0.18/0.37  cnf(c_0_18, plain, (r2_lattice3(X1,X2,X3)|X3!=k1_yellow_0(X1,X2)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_19, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_20, plain, (r1_yellow_0(X1,X2)|v2_struct_0(X1)|~v5_orders_2(X1)|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.37  cnf(c_0_21, negated_conjecture, (v3_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_22, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.18/0.37  fof(c_0_24, plain, ![X18, X19, X20]:(~l1_orders_2(X18)|(~r1_tarski(X19,X20)|~r2_yellow_0(X18,X19)|~r2_yellow_0(X18,X20)|r1_orders_2(X18,k2_yellow_0(X18,X20),k2_yellow_0(X18,X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_yellow_0])])])).
% 0.18/0.37  cnf(c_0_25, plain, (r2_lattice3(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.37  cnf(c_0_26, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]), c_0_19])).
% 0.18/0.37  cnf(c_0_27, negated_conjecture, (r1_yellow_0(esk2_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_16])]), c_0_23])).
% 0.18/0.37  cnf(c_0_28, plain, (r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))|~l1_orders_2(X1)|~r1_tarski(X2,X3)|~r2_yellow_0(X1,X2)|~r2_yellow_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.37  cnf(c_0_29, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  fof(c_0_30, plain, ![X5, X6, X7]:((~r3_orders_2(X5,X6,X7)|r1_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))&(~r1_orders_2(X5,X6,X7)|r3_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.18/0.37  cnf(c_0_31, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_32, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X3))|~r1_tarski(X2,X4)|~r2_lattice3(X1,X4,k1_yellow_0(X1,X3))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_25, c_0_19])).
% 0.18/0.37  cnf(c_0_33, negated_conjecture, (r2_lattice3(esk2_0,X1,k1_yellow_0(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_16])])).
% 0.18/0.37  cnf(c_0_34, negated_conjecture, (r1_orders_2(X1,k2_yellow_0(X1,esk4_0),k2_yellow_0(X1,esk3_0))|~r2_yellow_0(X1,esk4_0)|~r2_yellow_0(X1,esk3_0)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.37  cnf(c_0_35, plain, (r2_yellow_0(X1,X2)|v2_struct_0(X1)|~v5_orders_2(X1)|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.37  cnf(c_0_36, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.37  cnf(c_0_37, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]), c_0_19])).
% 0.18/0.37  cnf(c_0_38, negated_conjecture, (r2_lattice3(esk2_0,X1,k1_yellow_0(esk2_0,X2))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_16])])).
% 0.18/0.37  cnf(c_0_39, negated_conjecture, (r1_orders_2(X1,k2_yellow_0(X1,esk4_0),k2_yellow_0(X1,esk3_0))|v2_struct_0(X1)|~v3_lattice3(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_35])).
% 0.18/0.37  cnf(c_0_40, plain, (r3_orders_2(X1,X2,k1_yellow_0(X1,X3))|v2_struct_0(X1)|~r1_orders_2(X1,X2,k1_yellow_0(X1,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_36, c_0_19])).
% 0.18/0.37  cnf(c_0_41, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~r2_lattice3(X1,X2,k1_yellow_0(X1,X3))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_37, c_0_19])).
% 0.18/0.37  cnf(c_0_42, negated_conjecture, (r2_lattice3(esk2_0,esk3_0,k1_yellow_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_29])).
% 0.18/0.37  cnf(c_0_43, negated_conjecture, (~r3_orders_2(esk2_0,k1_yellow_0(esk2_0,esk3_0),k1_yellow_0(esk2_0,esk4_0))|~r1_orders_2(esk2_0,k2_yellow_0(esk2_0,esk4_0),k2_yellow_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_44, negated_conjecture, (r1_orders_2(esk2_0,k2_yellow_0(esk2_0,esk4_0),k2_yellow_0(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_21]), c_0_22]), c_0_16])]), c_0_23])).
% 0.18/0.37  cnf(c_0_45, plain, (r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|v2_struct_0(X1)|~r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_40, c_0_19])).
% 0.18/0.37  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk2_0,k1_yellow_0(esk2_0,esk3_0),k1_yellow_0(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_27]), c_0_16])])).
% 0.18/0.37  cnf(c_0_47, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_48, negated_conjecture, (~r3_orders_2(esk2_0,k1_yellow_0(esk2_0,esk3_0),k1_yellow_0(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.18/0.37  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_16]), c_0_47])]), c_0_48]), c_0_23]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 50
% 0.18/0.37  # Proof object clause steps            : 33
% 0.18/0.37  # Proof object formula steps           : 17
% 0.18/0.37  # Proof object conjectures             : 21
% 0.18/0.37  # Proof object clause conjectures      : 18
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 16
% 0.18/0.37  # Proof object initial formulas used   : 8
% 0.18/0.37  # Proof object generating inferences   : 14
% 0.18/0.37  # Proof object simplifying inferences  : 29
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 8
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 23
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 23
% 0.18/0.37  # Processed clauses                    : 67
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 0
% 0.18/0.37  # ...remaining for further processing  : 67
% 0.18/0.37  # Other redundant clauses eliminated   : 2
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 1
% 0.18/0.37  # Generated clauses                    : 25
% 0.18/0.37  # ...of the previous two non-trivial   : 24
% 0.18/0.37  # Contextual simplify-reflections      : 3
% 0.18/0.37  # Paramodulations                      : 23
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 2
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 41
% 0.18/0.37  #    Positive orientable unit clauses  : 14
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 2
% 0.18/0.37  #    Non-unit-clauses                  : 25
% 0.18/0.37  # Current number of unprocessed clauses: 3
% 0.18/0.37  # ...number of literals in the above   : 15
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 24
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 391
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 5
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.18/0.37  # Unit Clause-clause subsumption calls : 12
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 2
% 0.18/0.37  # BW rewrite match successes           : 1
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 2874
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.026 s
% 0.18/0.37  # System time              : 0.008 s
% 0.18/0.37  # Total time               : 0.035 s
% 0.18/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
