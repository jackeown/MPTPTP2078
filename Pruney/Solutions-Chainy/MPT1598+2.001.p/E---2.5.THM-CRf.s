%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:41 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 441 expanded)
%              Number of clauses        :   37 ( 163 expanded)
%              Number of leaves         :   11 ( 112 expanded)
%              Depth                    :   12
%              Number of atoms          :  274 (1704 expanded)
%              Number of equality atoms :   19 (  63 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   67 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_lattice3(k2_yellow_1(X1))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(t22_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k13_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

fof(commutativity_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k13_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k13_lattice3)).

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

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v1_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_yellow_1])).

fof(c_0_12,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | m1_subset_1(k10_lattice3(X16,X17,X18),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

fof(c_0_13,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v1_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X28] :
      ( v1_orders_2(k2_yellow_1(X28))
      & l1_orders_2(k2_yellow_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_15,plain,(
    ! [X19,X20,X21] :
      ( ~ v5_orders_2(X19)
      | ~ v1_lattice3(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | k13_lattice3(X19,X20,X21) = k10_lattice3(X19,X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

fof(c_0_16,plain,(
    ! [X29] :
      ( v1_orders_2(k2_yellow_1(X29))
      & v3_orders_2(k2_yellow_1(X29))
      & v4_orders_2(k2_yellow_1(X29))
      & v5_orders_2(k2_yellow_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_17,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( r1_orders_2(X22,X23,X25)
        | X25 != k13_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ v1_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,X24,X25)
        | X25 != k13_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ v1_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X22))
        | ~ r1_orders_2(X22,X23,X26)
        | ~ r1_orders_2(X22,X24,X26)
        | r1_orders_2(X22,X25,X26)
        | X25 != k13_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ v1_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk1_4(X22,X23,X24,X25),u1_struct_0(X22))
        | ~ r1_orders_2(X22,X23,X25)
        | ~ r1_orders_2(X22,X24,X25)
        | X25 = k13_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ v1_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,X23,esk1_4(X22,X23,X24,X25))
        | ~ r1_orders_2(X22,X23,X25)
        | ~ r1_orders_2(X22,X24,X25)
        | X25 = k13_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ v1_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,X24,esk1_4(X22,X23,X24,X25))
        | ~ r1_orders_2(X22,X23,X25)
        | ~ r1_orders_2(X22,X24,X25)
        | X25 = k13_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ v1_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X25,esk1_4(X22,X23,X24,X25))
        | ~ r1_orders_2(X22,X23,X25)
        | ~ r1_orders_2(X22,X24,X25)
        | X25 = k13_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ v1_lattice3(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_yellow_0])])])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k13_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k10_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),u1_struct_0(k2_yellow_1(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(esk2_0),X1,esk4_0) = k13_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_22]),c_0_23]),c_0_20])])).

fof(c_0_28,plain,(
    ! [X13,X14,X15] :
      ( ~ v5_orders_2(X13)
      | ~ v1_lattice3(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | k13_lattice3(X13,X14,X15) = k13_lattice3(X13,X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k13_lattice3])])).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,X2,k13_lattice3(X1,X3,X2))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(k13_lattice3(X1,X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) = k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_32,plain,
    ( k13_lattice3(X1,X2,X3) = k13_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r3_orders_2(X9,X10,X11)
        | r1_orders_2(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ l1_orders_2(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) )
      & ( ~ r1_orders_2(X9,X10,X11)
        | r3_orders_2(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ l1_orders_2(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),X1,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),u1_struct_0(k2_yellow_1(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_22]),c_0_23]),c_0_20])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k13_lattice3(k2_yellow_1(esk2_0),X1,esk4_0) = k13_lattice3(k2_yellow_1(esk2_0),esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_22]),c_0_23]),c_0_20])])).

fof(c_0_37,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | ~ v1_lattice3(X12)
      | ~ v2_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_38,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_35])])).

cnf(c_0_40,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),X1,k13_lattice3(k2_yellow_1(esk2_0),esk4_0,X1))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk4_0,X1),u1_struct_0(k2_yellow_1(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_19]),c_0_22]),c_0_23]),c_0_20])])).

cnf(c_0_42,negated_conjecture,
    ( k13_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0) = k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

fof(c_0_43,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r3_orders_2(k2_yellow_1(X30),X31,X32)
        | r1_tarski(X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))
        | v1_xboole_0(X30) )
      & ( ~ r1_tarski(X31,X32)
        | r3_orders_2(k2_yellow_1(X30),X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))
        | v1_xboole_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_44,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_35]),c_0_19]),c_0_20]),c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_42]),c_0_42]),c_0_35])])).

fof(c_0_47,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X7)
      | r1_tarski(k2_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_48,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_23]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_46]),c_0_35]),c_0_26]),c_0_20]),c_0_40])])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_35]),c_0_19])]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_51]),c_0_23]),c_0_20])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk4_0),k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | ~ r1_tarski(X1,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_54]),c_0_35]),c_0_26])]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:23:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.50/0.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.50/0.66  # and selection function SelectCQArNTNpEqFirst.
% 0.50/0.66  #
% 0.50/0.66  # Preprocessing time       : 0.029 s
% 0.50/0.66  # Presaturation interreduction done
% 0.50/0.66  
% 0.50/0.66  # Proof found!
% 0.50/0.66  # SZS status Theorem
% 0.50/0.66  # SZS output start CNFRefutation
% 0.50/0.66  fof(t6_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v1_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_1)).
% 0.50/0.66  fof(dt_k10_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 0.50/0.66  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.50/0.66  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.50/0.66  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.50/0.66  fof(t22_yellow_0, axiom, ![X1]:(((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k13_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_yellow_0)).
% 0.50/0.66  fof(commutativity_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k13_lattice3(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k13_lattice3)).
% 0.50/0.66  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.50/0.66  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.50/0.66  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.50/0.66  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.50/0.66  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v1_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t6_yellow_1])).
% 0.50/0.66  fof(c_0_12, plain, ![X16, X17, X18]:(~l1_orders_2(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|m1_subset_1(k10_lattice3(X16,X17,X18),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).
% 0.50/0.66  fof(c_0_13, negated_conjecture, (~v1_xboole_0(esk2_0)&(v1_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.50/0.66  fof(c_0_14, plain, ![X28]:(v1_orders_2(k2_yellow_1(X28))&l1_orders_2(k2_yellow_1(X28))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.50/0.66  fof(c_0_15, plain, ![X19, X20, X21]:(~v5_orders_2(X19)|~v1_lattice3(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|k13_lattice3(X19,X20,X21)=k10_lattice3(X19,X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.50/0.66  fof(c_0_16, plain, ![X29]:(((v1_orders_2(k2_yellow_1(X29))&v3_orders_2(k2_yellow_1(X29)))&v4_orders_2(k2_yellow_1(X29)))&v5_orders_2(k2_yellow_1(X29))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.50/0.66  fof(c_0_17, plain, ![X22, X23, X24, X25, X26]:((((r1_orders_2(X22,X23,X25)|X25!=k13_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~v1_lattice3(X22)|~l1_orders_2(X22)))&(r1_orders_2(X22,X24,X25)|X25!=k13_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~v1_lattice3(X22)|~l1_orders_2(X22))))&(~m1_subset_1(X26,u1_struct_0(X22))|(~r1_orders_2(X22,X23,X26)|~r1_orders_2(X22,X24,X26)|r1_orders_2(X22,X25,X26))|X25!=k13_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~v1_lattice3(X22)|~l1_orders_2(X22))))&((m1_subset_1(esk1_4(X22,X23,X24,X25),u1_struct_0(X22))|(~r1_orders_2(X22,X23,X25)|~r1_orders_2(X22,X24,X25))|X25=k13_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~v1_lattice3(X22)|~l1_orders_2(X22)))&(((r1_orders_2(X22,X23,esk1_4(X22,X23,X24,X25))|(~r1_orders_2(X22,X23,X25)|~r1_orders_2(X22,X24,X25))|X25=k13_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~v1_lattice3(X22)|~l1_orders_2(X22)))&(r1_orders_2(X22,X24,esk1_4(X22,X23,X24,X25))|(~r1_orders_2(X22,X23,X25)|~r1_orders_2(X22,X24,X25))|X25=k13_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~v1_lattice3(X22)|~l1_orders_2(X22))))&(~r1_orders_2(X22,X25,esk1_4(X22,X23,X24,X25))|(~r1_orders_2(X22,X23,X25)|~r1_orders_2(X22,X24,X25))|X25=k13_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~v1_lattice3(X22)|~l1_orders_2(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_yellow_0])])])])])).
% 0.50/0.66  cnf(c_0_18, plain, (m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.50/0.66  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.50/0.66  cnf(c_0_20, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.50/0.66  cnf(c_0_21, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.66  cnf(c_0_22, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.66  cnf(c_0_23, negated_conjecture, (v1_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.50/0.66  cnf(c_0_24, plain, (r1_orders_2(X1,X2,X3)|X3!=k13_lattice3(X1,X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.66  cnf(c_0_25, negated_conjecture, (m1_subset_1(k10_lattice3(k2_yellow_1(esk2_0),X1,esk4_0),u1_struct_0(k2_yellow_1(esk2_0)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.50/0.66  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.50/0.66  cnf(c_0_27, negated_conjecture, (k10_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)=k13_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_19]), c_0_22]), c_0_23]), c_0_20])])).
% 0.50/0.66  fof(c_0_28, plain, ![X13, X14, X15]:(~v5_orders_2(X13)|~v1_lattice3(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))|k13_lattice3(X13,X14,X15)=k13_lattice3(X13,X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k13_lattice3])])).
% 0.50/0.66  cnf(c_0_29, plain, (r1_orders_2(X1,X2,k13_lattice3(X1,X3,X2))|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(k13_lattice3(X1,X3,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_24])).
% 0.50/0.66  cnf(c_0_30, negated_conjecture, (m1_subset_1(k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),u1_struct_0(k2_yellow_1(esk2_0)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.50/0.66  cnf(c_0_31, negated_conjecture, (k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)=k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.50/0.66  cnf(c_0_32, plain, (k13_lattice3(X1,X2,X3)=k13_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.50/0.66  fof(c_0_33, plain, ![X9, X10, X11]:((~r3_orders_2(X9,X10,X11)|r1_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))&(~r1_orders_2(X9,X10,X11)|r3_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.50/0.66  cnf(c_0_34, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),X1,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1))|~m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),u1_struct_0(k2_yellow_1(esk2_0)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_26]), c_0_22]), c_0_23]), c_0_20])])).
% 0.50/0.66  cnf(c_0_35, negated_conjecture, (m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),u1_struct_0(k2_yellow_1(esk2_0)))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.50/0.66  cnf(c_0_36, negated_conjecture, (k13_lattice3(k2_yellow_1(esk2_0),X1,esk4_0)=k13_lattice3(k2_yellow_1(esk2_0),esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_19]), c_0_22]), c_0_23]), c_0_20])])).
% 0.50/0.66  fof(c_0_37, plain, ![X12]:(~l1_orders_2(X12)|(~v1_lattice3(X12)|~v2_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.50/0.66  cnf(c_0_38, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.50/0.66  cnf(c_0_39, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_19]), c_0_35])])).
% 0.50/0.66  cnf(c_0_40, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.66  cnf(c_0_41, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),X1,k13_lattice3(k2_yellow_1(esk2_0),esk4_0,X1))|~m1_subset_1(k13_lattice3(k2_yellow_1(esk2_0),esk4_0,X1),u1_struct_0(k2_yellow_1(esk2_0)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_19]), c_0_22]), c_0_23]), c_0_20])])).
% 0.50/0.66  cnf(c_0_42, negated_conjecture, (k13_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0)=k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 0.50/0.66  fof(c_0_43, plain, ![X30, X31, X32]:((~r3_orders_2(k2_yellow_1(X30),X31,X32)|r1_tarski(X31,X32)|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))|~m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))|v1_xboole_0(X30))&(~r1_tarski(X31,X32)|r3_orders_2(k2_yellow_1(X30),X31,X32)|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))|~m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))|v1_xboole_0(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.50/0.66  cnf(c_0_44, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.50/0.66  cnf(c_0_45, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_35]), c_0_19]), c_0_20]), c_0_40])])).
% 0.50/0.66  cnf(c_0_46, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_42]), c_0_42]), c_0_35])])).
% 0.50/0.66  fof(c_0_47, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X7)|r1_tarski(k2_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.50/0.66  cnf(c_0_48, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.50/0.66  cnf(c_0_49, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_23]), c_0_20])])).
% 0.50/0.66  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.50/0.66  cnf(c_0_51, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_46]), c_0_35]), c_0_26]), c_0_20]), c_0_40])])).
% 0.50/0.66  cnf(c_0_52, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.50/0.66  cnf(c_0_53, negated_conjecture, (r1_tarski(esk4_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_35]), c_0_19])]), c_0_50])).
% 0.50/0.66  cnf(c_0_54, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_51]), c_0_23]), c_0_20])])).
% 0.50/0.66  cnf(c_0_55, negated_conjecture, (~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.50/0.66  cnf(c_0_56, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk4_0),k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|~r1_tarski(X1,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.50/0.66  cnf(c_0_57, negated_conjecture, (r1_tarski(esk3_0,k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_54]), c_0_35]), c_0_26])]), c_0_50])).
% 0.50/0.66  cnf(c_0_58, negated_conjecture, (~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_55, c_0_31])).
% 0.50/0.66  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), ['proof']).
% 0.50/0.66  # SZS output end CNFRefutation
% 0.50/0.66  # Proof object total steps             : 60
% 0.50/0.66  # Proof object clause steps            : 37
% 0.50/0.66  # Proof object formula steps           : 23
% 0.50/0.66  # Proof object conjectures             : 28
% 0.50/0.66  # Proof object clause conjectures      : 25
% 0.50/0.66  # Proof object formula conjectures     : 3
% 0.50/0.66  # Proof object initial clauses used    : 16
% 0.50/0.66  # Proof object initial formulas used   : 11
% 0.50/0.66  # Proof object generating inferences   : 18
% 0.50/0.66  # Proof object simplifying inferences  : 52
% 0.50/0.66  # Training examples: 0 positive, 0 negative
% 0.50/0.66  # Parsed axioms                        : 11
% 0.50/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.66  # Initial clauses                      : 27
% 0.50/0.66  # Removed in clause preprocessing      : 0
% 0.50/0.66  # Initial clauses in saturation        : 27
% 0.50/0.66  # Processed clauses                    : 1122
% 0.50/0.66  # ...of these trivial                  : 90
% 0.50/0.66  # ...subsumed                          : 103
% 0.50/0.66  # ...remaining for further processing  : 929
% 0.50/0.66  # Other redundant clauses eliminated   : 3
% 0.50/0.66  # Clauses deleted for lack of memory   : 0
% 0.50/0.66  # Backward-subsumed                    : 0
% 0.50/0.66  # Backward-rewritten                   : 307
% 0.50/0.66  # Generated clauses                    : 28058
% 0.50/0.66  # ...of the previous two non-trivial   : 28306
% 0.50/0.66  # Contextual simplify-reflections      : 0
% 0.50/0.66  # Paramodulations                      : 28055
% 0.50/0.66  # Factorizations                       : 0
% 0.50/0.66  # Equation resolutions                 : 3
% 0.50/0.66  # Propositional unsat checks           : 0
% 0.50/0.66  #    Propositional check models        : 0
% 0.50/0.66  #    Propositional check unsatisfiable : 0
% 0.50/0.66  #    Propositional clauses             : 0
% 0.50/0.66  #    Propositional clauses after purity: 0
% 0.50/0.66  #    Propositional unsat core size     : 0
% 0.50/0.66  #    Propositional preprocessing time  : 0.000
% 0.50/0.66  #    Propositional encoding time       : 0.000
% 0.50/0.66  #    Propositional solver time         : 0.000
% 0.50/0.66  #    Success case prop preproc time    : 0.000
% 0.50/0.66  #    Success case prop encoding time   : 0.000
% 0.50/0.66  #    Success case prop solver time     : 0.000
% 0.50/0.66  # Current number of processed clauses  : 593
% 0.50/0.66  #    Positive orientable unit clauses  : 232
% 0.50/0.66  #    Positive unorientable unit clauses: 0
% 0.50/0.66  #    Negative unit clauses             : 2
% 0.50/0.66  #    Non-unit-clauses                  : 359
% 0.50/0.66  # Current number of unprocessed clauses: 25959
% 0.50/0.66  # ...number of literals in the above   : 41882
% 0.50/0.66  # Current number of archived formulas  : 0
% 0.50/0.66  # Current number of archived clauses   : 333
% 0.50/0.66  # Clause-clause subsumption calls (NU) : 24058
% 0.50/0.66  # Rec. Clause-clause subsumption calls : 23707
% 0.50/0.66  # Non-unit clause-clause subsumptions  : 103
% 0.50/0.66  # Unit Clause-clause subsumption calls : 8232
% 0.50/0.66  # Rewrite failures with RHS unbound    : 0
% 0.50/0.66  # BW rewrite match attempts            : 10115
% 0.50/0.66  # BW rewrite match successes           : 26
% 0.50/0.66  # Condensation attempts                : 0
% 0.50/0.66  # Condensation successes               : 0
% 0.50/0.66  # Termbank termtop insertions          : 1484406
% 0.50/0.66  
% 0.50/0.66  # -------------------------------------------------
% 0.50/0.66  # User time                : 0.309 s
% 0.50/0.66  # System time              : 0.016 s
% 0.50/0.66  # Total time               : 0.325 s
% 0.50/0.66  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
