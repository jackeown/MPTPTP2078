%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:42 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 275 expanded)
%              Number of clauses        :   35 ( 106 expanded)
%              Number of leaves         :   10 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  263 (1126 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   67 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

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

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v1_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_yellow_1])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] :
      ( ~ v5_orders_2(X15)
      | ~ v1_lattice3(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | k13_lattice3(X15,X16,X17) = k10_lattice3(X15,X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

fof(c_0_12,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v1_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X25] :
      ( v1_orders_2(k2_yellow_1(X25))
      & v3_orders_2(k2_yellow_1(X25))
      & v4_orders_2(k2_yellow_1(X25))
      & v5_orders_2(k2_yellow_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_14,plain,(
    ! [X24] :
      ( v1_orders_2(k2_yellow_1(X24))
      & l1_orders_2(k2_yellow_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

cnf(c_0_15,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X12,X13,X14] :
      ( ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | m1_subset_1(k10_lattice3(X12,X13,X14),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

cnf(c_0_20,negated_conjecture,
    ( k13_lattice3(k2_yellow_1(esk2_0),X1,X2) = k10_lattice3(k2_yellow_1(esk2_0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( r1_orders_2(X18,X19,X21)
        | X21 != k13_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ v1_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,X20,X21)
        | X21 != k13_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ v1_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X18))
        | ~ r1_orders_2(X18,X19,X22)
        | ~ r1_orders_2(X18,X20,X22)
        | r1_orders_2(X18,X21,X22)
        | X21 != k13_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ v1_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk1_4(X18,X19,X20,X21),u1_struct_0(X18))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | X21 = k13_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ v1_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,X19,esk1_4(X18,X19,X20,X21))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | X21 = k13_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ v1_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,X20,esk1_4(X18,X19,X20,X21))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | X21 = k13_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ v1_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ r1_orders_2(X18,X21,esk1_4(X18,X19,X20,X21))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | X21 = k13_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v5_orders_2(X18)
        | ~ v1_lattice3(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_yellow_0])])])])])).

cnf(c_0_24,negated_conjecture,
    ( k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1) = k10_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( m1_subset_1(k10_lattice3(k2_yellow_1(X1),X2,X3),u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k13_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) = k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k10_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),u1_struct_0(k2_yellow_1(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_31,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk4_0,X1)
    | X1 != k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16]),c_0_17]),c_0_21]),c_0_25]),c_0_18])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k13_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
    ! [X26] :
      ( ( ~ v2_struct_0(k2_yellow_1(X26))
        | v1_xboole_0(X26) )
      & ( v1_orders_2(k2_yellow_1(X26))
        | v1_xboole_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_37,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk3_0,X1)
    | X1 != k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_16]),c_0_17]),c_0_25]),c_0_21]),c_0_18])])).

fof(c_0_40,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r3_orders_2(k2_yellow_1(X27),X28,X29)
        | r1_tarski(X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))
        | ~ m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))
        | v1_xboole_0(X27) )
      & ( ~ r1_tarski(X28,X29)
        | r3_orders_2(k2_yellow_1(X27),X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))
        | ~ m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))
        | v1_xboole_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_34]),c_0_25])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_34])])).

fof(c_0_45,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X7)
      | r1_tarski(k2_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_46,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_44]),c_0_34]),c_0_21])])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_34]),c_0_25])]),c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_48]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | ~ r1_tarski(X1,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_51]),c_0_34]),c_0_21])]),c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.49  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.21/0.49  # and selection function SelectNegativeLiterals.
% 0.21/0.49  #
% 0.21/0.49  # Preprocessing time       : 0.027 s
% 0.21/0.49  # Presaturation interreduction done
% 0.21/0.49  
% 0.21/0.49  # Proof found!
% 0.21/0.49  # SZS status Theorem
% 0.21/0.49  # SZS output start CNFRefutation
% 0.21/0.49  fof(t6_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v1_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_1)).
% 0.21/0.49  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.21/0.49  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.21/0.49  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.21/0.49  fof(dt_k10_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 0.21/0.49  fof(t22_yellow_0, axiom, ![X1]:(((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k13_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_yellow_0)).
% 0.21/0.49  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.21/0.49  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.21/0.49  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.21/0.49  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.21/0.49  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v1_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t6_yellow_1])).
% 0.21/0.49  fof(c_0_11, plain, ![X15, X16, X17]:(~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|k13_lattice3(X15,X16,X17)=k10_lattice3(X15,X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.21/0.49  fof(c_0_12, negated_conjecture, (~v1_xboole_0(esk2_0)&(v1_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.21/0.49  fof(c_0_13, plain, ![X25]:(((v1_orders_2(k2_yellow_1(X25))&v3_orders_2(k2_yellow_1(X25)))&v4_orders_2(k2_yellow_1(X25)))&v5_orders_2(k2_yellow_1(X25))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.21/0.49  fof(c_0_14, plain, ![X24]:(v1_orders_2(k2_yellow_1(X24))&l1_orders_2(k2_yellow_1(X24))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.21/0.49  cnf(c_0_15, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.49  cnf(c_0_16, negated_conjecture, (v1_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.49  cnf(c_0_17, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.49  cnf(c_0_18, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.49  fof(c_0_19, plain, ![X12, X13, X14]:(~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|m1_subset_1(k10_lattice3(X12,X13,X14),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).
% 0.21/0.49  cnf(c_0_20, negated_conjecture, (k13_lattice3(k2_yellow_1(esk2_0),X1,X2)=k10_lattice3(k2_yellow_1(esk2_0),X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(esk2_0)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.21/0.49  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.49  cnf(c_0_22, plain, (m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.49  fof(c_0_23, plain, ![X18, X19, X20, X21, X22]:((((r1_orders_2(X18,X19,X21)|X21!=k13_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~v1_lattice3(X18)|~l1_orders_2(X18)))&(r1_orders_2(X18,X20,X21)|X21!=k13_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~v1_lattice3(X18)|~l1_orders_2(X18))))&(~m1_subset_1(X22,u1_struct_0(X18))|(~r1_orders_2(X18,X19,X22)|~r1_orders_2(X18,X20,X22)|r1_orders_2(X18,X21,X22))|X21!=k13_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~v1_lattice3(X18)|~l1_orders_2(X18))))&((m1_subset_1(esk1_4(X18,X19,X20,X21),u1_struct_0(X18))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21))|X21=k13_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~v1_lattice3(X18)|~l1_orders_2(X18)))&(((r1_orders_2(X18,X19,esk1_4(X18,X19,X20,X21))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21))|X21=k13_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~v1_lattice3(X18)|~l1_orders_2(X18)))&(r1_orders_2(X18,X20,esk1_4(X18,X19,X20,X21))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21))|X21=k13_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~v1_lattice3(X18)|~l1_orders_2(X18))))&(~r1_orders_2(X18,X21,esk1_4(X18,X19,X20,X21))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21))|X21=k13_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(~v5_orders_2(X18)|~v1_lattice3(X18)|~l1_orders_2(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_yellow_0])])])])])).
% 0.21/0.49  cnf(c_0_24, negated_conjecture, (k13_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)=k10_lattice3(k2_yellow_1(esk2_0),esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.49  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.49  cnf(c_0_26, plain, (m1_subset_1(k10_lattice3(k2_yellow_1(X1),X2,X3),u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.21/0.49  fof(c_0_27, plain, ![X9, X10, X11]:((~r3_orders_2(X9,X10,X11)|r1_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))&(~r1_orders_2(X9,X10,X11)|r3_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.21/0.49  cnf(c_0_28, plain, (r1_orders_2(X1,X2,X3)|X3!=k13_lattice3(X1,X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.49  cnf(c_0_29, negated_conjecture, (k13_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)=k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.49  cnf(c_0_30, negated_conjecture, (m1_subset_1(k10_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),u1_struct_0(k2_yellow_1(esk2_0)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.21/0.49  cnf(c_0_31, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.49  cnf(c_0_32, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.49  cnf(c_0_33, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk4_0,X1)|X1!=k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_16]), c_0_17]), c_0_21]), c_0_25]), c_0_18])])).
% 0.21/0.49  cnf(c_0_34, negated_conjecture, (m1_subset_1(k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),u1_struct_0(k2_yellow_1(esk2_0)))), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 0.21/0.49  cnf(c_0_35, plain, (r1_orders_2(X1,X2,X3)|X3!=k13_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.49  fof(c_0_36, plain, ![X26]:((~v2_struct_0(k2_yellow_1(X26))|v1_xboole_0(X26))&(v1_orders_2(k2_yellow_1(X26))|v1_xboole_0(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.21/0.49  cnf(c_0_37, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_32])])).
% 0.21/0.49  cnf(c_0_38, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_34])])).
% 0.21/0.49  cnf(c_0_39, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk3_0,X1)|X1!=k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_16]), c_0_17]), c_0_25]), c_0_21]), c_0_18])])).
% 0.21/0.49  fof(c_0_40, plain, ![X27, X28, X29]:((~r3_orders_2(k2_yellow_1(X27),X28,X29)|r1_tarski(X28,X29)|~m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))|~m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))|v1_xboole_0(X27))&(~r1_tarski(X28,X29)|r3_orders_2(k2_yellow_1(X27),X28,X29)|~m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))|~m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))|v1_xboole_0(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.21/0.49  cnf(c_0_41, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.49  cnf(c_0_42, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_34]), c_0_25])])).
% 0.21/0.49  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.49  cnf(c_0_44, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_34])])).
% 0.21/0.49  fof(c_0_45, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X7)|r1_tarski(k2_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.21/0.49  cnf(c_0_46, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.49  cnf(c_0_47, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.21/0.49  cnf(c_0_48, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_44]), c_0_34]), c_0_21])])).
% 0.21/0.49  cnf(c_0_49, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.49  cnf(c_0_50, negated_conjecture, (r1_tarski(esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_34]), c_0_25])]), c_0_43])).
% 0.21/0.49  cnf(c_0_51, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_48]), c_0_43])).
% 0.21/0.49  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|~r1_tarski(X1,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.49  cnf(c_0_53, negated_conjecture, (r1_tarski(esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_51]), c_0_34]), c_0_21])]), c_0_43])).
% 0.21/0.49  cnf(c_0_54, negated_conjecture, (~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.49  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 0.21/0.49  # SZS output end CNFRefutation
% 0.21/0.49  # Proof object total steps             : 56
% 0.21/0.49  # Proof object clause steps            : 35
% 0.21/0.49  # Proof object formula steps           : 21
% 0.21/0.49  # Proof object conjectures             : 25
% 0.21/0.49  # Proof object clause conjectures      : 22
% 0.21/0.49  # Proof object formula conjectures     : 3
% 0.21/0.49  # Proof object initial clauses used    : 16
% 0.21/0.49  # Proof object initial formulas used   : 10
% 0.21/0.49  # Proof object generating inferences   : 19
% 0.21/0.49  # Proof object simplifying inferences  : 38
% 0.21/0.49  # Training examples: 0 positive, 0 negative
% 0.21/0.49  # Parsed axioms                        : 10
% 0.21/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.49  # Initial clauses                      : 27
% 0.21/0.49  # Removed in clause preprocessing      : 0
% 0.21/0.49  # Initial clauses in saturation        : 27
% 0.21/0.49  # Processed clauses                    : 722
% 0.21/0.49  # ...of these trivial                  : 1
% 0.21/0.49  # ...subsumed                          : 1
% 0.21/0.49  # ...remaining for further processing  : 720
% 0.21/0.49  # Other redundant clauses eliminated   : 0
% 0.21/0.49  # Clauses deleted for lack of memory   : 0
% 0.21/0.49  # Backward-subsumed                    : 0
% 0.21/0.49  # Backward-rewritten                   : 6
% 0.21/0.49  # Generated clauses                    : 8649
% 0.21/0.49  # ...of the previous two non-trivial   : 8574
% 0.21/0.49  # Contextual simplify-reflections      : 0
% 0.21/0.49  # Paramodulations                      : 8637
% 0.21/0.49  # Factorizations                       : 0
% 0.21/0.49  # Equation resolutions                 : 12
% 0.21/0.49  # Propositional unsat checks           : 0
% 0.21/0.49  #    Propositional check models        : 0
% 0.21/0.49  #    Propositional check unsatisfiable : 0
% 0.21/0.49  #    Propositional clauses             : 0
% 0.21/0.49  #    Propositional clauses after purity: 0
% 0.21/0.49  #    Propositional unsat core size     : 0
% 0.21/0.49  #    Propositional preprocessing time  : 0.000
% 0.21/0.49  #    Propositional encoding time       : 0.000
% 0.21/0.49  #    Propositional solver time         : 0.000
% 0.21/0.49  #    Success case prop preproc time    : 0.000
% 0.21/0.49  #    Success case prop encoding time   : 0.000
% 0.21/0.49  #    Success case prop solver time     : 0.000
% 0.21/0.49  # Current number of processed clauses  : 689
% 0.21/0.49  #    Positive orientable unit clauses  : 588
% 0.21/0.49  #    Positive unorientable unit clauses: 0
% 0.21/0.49  #    Negative unit clauses             : 2
% 0.21/0.49  #    Non-unit-clauses                  : 99
% 0.21/0.49  # Current number of unprocessed clauses: 7901
% 0.21/0.49  # ...number of literals in the above   : 10818
% 0.21/0.49  # Current number of archived formulas  : 0
% 0.21/0.49  # Current number of archived clauses   : 31
% 0.21/0.49  # Clause-clause subsumption calls (NU) : 2505
% 0.21/0.49  # Rec. Clause-clause subsumption calls : 1361
% 0.21/0.49  # Non-unit clause-clause subsumptions  : 1
% 0.21/0.49  # Unit Clause-clause subsumption calls : 1389
% 0.21/0.49  # Rewrite failures with RHS unbound    : 0
% 0.21/0.49  # BW rewrite match attempts            : 24838
% 0.21/0.49  # BW rewrite match successes           : 6
% 0.21/0.49  # Condensation attempts                : 0
% 0.21/0.49  # Condensation successes               : 0
% 0.21/0.49  # Termbank termtop insertions          : 229348
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.137 s
% 0.21/0.49  # System time              : 0.007 s
% 0.21/0.49  # Total time               : 0.144 s
% 0.21/0.49  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
