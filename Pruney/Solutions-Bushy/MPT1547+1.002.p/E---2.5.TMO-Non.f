%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1547+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:22 EST 2020

% Result     : Timeout 57.78s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   63 (1227 expanded)
%              Number of clauses        :   50 ( 410 expanded)
%              Number of leaves         :    6 ( 294 expanded)
%              Depth                    :   12
%              Number of atoms          :  325 (8255 expanded)
%              Number of equality atoms :   33 (1048 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   67 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_yellow_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X2 = k12_lattice3(X1,X2,X3)
              <=> r3_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(dt_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

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

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(t23_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k12_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v5_orders_2(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( X2 = k12_lattice3(X1,X2,X3)
                <=> r3_orders_2(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_yellow_0])).

fof(c_0_7,plain,(
    ! [X13,X14,X15] :
      ( v2_struct_0(X13)
      | ~ v3_orders_2(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | r3_orders_2(X13,X14,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_8,negated_conjecture,
    ( v3_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & v2_lattice3(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ( esk3_0 != k12_lattice3(esk2_0,esk3_0,esk4_0)
      | ~ r3_orders_2(esk2_0,esk3_0,esk4_0) )
    & ( esk3_0 = k12_lattice3(esk2_0,esk3_0,esk4_0)
      | r3_orders_2(esk2_0,esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ~ v5_orders_2(X7)
      | ~ v2_lattice3(X7)
      | ~ l1_orders_2(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | m1_subset_1(k12_lattice3(X7,X8,X9),u1_struct_0(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).

cnf(c_0_10,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r3_orders_2(X10,X11,X12)
        | r1_orders_2(X10,X11,X12)
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10)) )
      & ( ~ r1_orders_2(X10,X11,X12)
        | r3_orders_2(X10,X11,X12)
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( v2_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_18,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_19,negated_conjecture,
    ( r3_orders_2(esk2_0,X1,X1)
    | v2_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( r1_orders_2(X16,X19,X17)
        | X19 != k12_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,X19,X18)
        | X19 != k12_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X16))
        | ~ r1_orders_2(X16,X20,X17)
        | ~ r1_orders_2(X16,X20,X18)
        | r1_orders_2(X16,X20,X19)
        | X19 != k12_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk1_4(X16,X17,X18,X19),u1_struct_0(X16))
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k12_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,esk1_4(X16,X17,X18,X19),X17)
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k12_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,esk1_4(X16,X17,X18,X19),X18)
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k12_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,esk1_4(X16,X17,X18,X19),X19)
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k12_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_yellow_0])])])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k12_lattice3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_11]),c_0_16]),c_0_17]),c_0_13])])).

cnf(c_0_24,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r3_orders_2(esk2_0,esk3_0,esk3_0)
    | v2_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | v2_struct_0(esk2_0)
    | ~ r3_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_27,negated_conjecture,
    ( esk3_0 = k12_lattice3(esk2_0,esk3_0,esk4_0)
    | r3_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k12_lattice3(esk2_0,X1,esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_20]),c_0_16]),c_0_17]),c_0_13])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k12_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk3_0)
    | v2_struct_0(esk2_0)
    | ~ r3_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_12]),c_0_13])])).

cnf(c_0_32,negated_conjecture,
    ( r3_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_17]),c_0_13])])).

cnf(c_0_33,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X2)
    | X4 = k12_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( X4 = k12_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_20])])).

cnf(c_0_36,plain,
    ( r1_orders_2(X1,k12_lattice3(X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k12_lattice3(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_20])])).

cnf(c_0_39,negated_conjecture,
    ( k12_lattice3(esk2_0,X1,X2) = esk3_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,X2,esk3_0),X1)
    | ~ r1_orders_2(esk2_0,esk3_0,X2)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_20]),c_0_16]),c_0_17]),c_0_13])])).

cnf(c_0_40,negated_conjecture,
    ( k12_lattice3(esk2_0,X1,X2) = esk3_0
    | ~ r1_orders_2(esk2_0,esk1_4(esk2_0,X1,X2,esk3_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,X2)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_16]),c_0_17]),c_0_13])])).

cnf(c_0_41,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_35]),c_0_17]),c_0_13])])).

cnf(c_0_42,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk2_0,k12_lattice3(esk2_0,k12_lattice3(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk3_0),X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_16]),c_0_17]),c_0_13])])).

cnf(c_0_44,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X3)
    | X4 = k12_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_38]),c_0_17]),c_0_13])])).

cnf(c_0_46,negated_conjecture,
    ( k12_lattice3(esk2_0,X1,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk3_0),X1)
    | ~ r1_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | k12_lattice3(esk2_0,X1,esk4_0) = esk3_0
    | ~ r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk3_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_11])])).

cnf(c_0_48,negated_conjecture,
    ( r3_orders_2(esk2_0,X1,esk4_0)
    | v2_struct_0(esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk2_0,k12_lattice3(esk2_0,k12_lattice3(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk3_0),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k12_lattice3(esk2_0,k12_lattice3(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk3_0),esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( k12_lattice3(esk2_0,X1,X2) = esk3_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,X2,esk3_0),X2)
    | ~ r1_orders_2(esk2_0,esk3_0,X2)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_16]),c_0_17]),c_0_13])])).

cnf(c_0_52,negated_conjecture,
    ( k12_lattice3(esk2_0,X1,esk3_0) = esk3_0
    | ~ r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk3_0,esk3_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_45]),c_0_20])])).

cnf(c_0_53,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | k12_lattice3(esk2_0,X1,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk3_0),X1)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ r1_orders_2(esk2_0,esk1_4(esk2_0,esk3_0,esk4_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_20])])).

cnf(c_0_55,negated_conjecture,
    ( r3_orders_2(esk2_0,k12_lattice3(esk2_0,k12_lattice3(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk3_0),esk4_0),esk4_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_56,negated_conjecture,
    ( k12_lattice3(esk2_0,X1,esk3_0) = esk3_0
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_20]),c_0_45])]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( esk3_0 != k12_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ r3_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_58,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_20]),c_0_45])]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r3_orders_2(esk2_0,k12_lattice3(esk2_0,k12_lattice3(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk3_0),esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_55]),c_0_17]),c_0_13])])).

cnf(c_0_60,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_45]),c_0_20])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r3_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_58]),c_0_60]),c_0_58]),c_0_61]),
    [proof]).

%------------------------------------------------------------------------------
