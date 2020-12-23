%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1561+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:24 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 513 expanded)
%              Number of clauses        :   48 ( 167 expanded)
%              Number of leaves         :    9 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  380 (3222 expanded)
%              Number of equality atoms :   54 ( 652 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_0)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

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

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t7_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X2,X3) )
                & ( r1_orders_2(X1,X2,X3)
                 => r1_lattice3(X1,k1_tarski(X3),X2) )
                & ( r2_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X3,X2) )
                & ( r1_orders_2(X1,X3,X2)
                 => r2_lattice3(X1,k1_tarski(X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

fof(t31_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) )
               => ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) )
              & ( ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) )
               => ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
              & k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_yellow_0])).

fof(c_0_10,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( r2_lattice3(X15,X17,X16)
        | X16 != k1_yellow_0(X15,X17)
        | ~ r1_yellow_0(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_lattice3(X15,X17,X18)
        | r1_orders_2(X15,X16,X18)
        | X16 != k1_yellow_0(X15,X17)
        | ~ r1_yellow_0(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k1_yellow_0(X15,X19)
        | m1_subset_1(esk1_3(X15,X16,X19),u1_struct_0(X15))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_yellow_0(X15,X19)
        | m1_subset_1(esk1_3(X15,X16,X19),u1_struct_0(X15))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k1_yellow_0(X15,X19)
        | r2_lattice3(X15,X19,esk1_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_yellow_0(X15,X19)
        | r2_lattice3(X15,X19,esk1_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k1_yellow_0(X15,X19)
        | ~ r1_orders_2(X15,X16,esk1_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_yellow_0(X15,X19)
        | ~ r1_orders_2(X15,X16,esk1_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ( k1_yellow_0(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) != esk4_0
      | k2_yellow_0(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
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

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v3_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | r3_orders_2(X12,X13,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_14,plain,(
    ! [X7,X8] :
      ( v1_xboole_0(X7)
      | ~ m1_subset_1(X8,X7)
      | k6_domain_1(X7,X8) = k1_tarski(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_15,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk1_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_lattice3(X27,k1_tarski(X29),X28)
        | r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,X28,X29)
        | r1_lattice3(X27,k1_tarski(X29),X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r2_lattice3(X27,k1_tarski(X29),X28)
        | r1_orders_2(X27,X29,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,X29,X28)
        | r2_lattice3(X27,k1_tarski(X29),X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_25,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( r1_lattice3(X21,X23,X22)
        | X22 != k2_yellow_0(X21,X23)
        | ~ r2_yellow_0(X21,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r1_lattice3(X21,X23,X24)
        | r1_orders_2(X21,X24,X22)
        | X22 != k2_yellow_0(X21,X23)
        | ~ r2_yellow_0(X21,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( X22 = k2_yellow_0(X21,X25)
        | m1_subset_1(esk2_3(X21,X22,X25),u1_struct_0(X21))
        | ~ r1_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r2_yellow_0(X21,X25)
        | m1_subset_1(esk2_3(X21,X22,X25),u1_struct_0(X21))
        | ~ r1_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( X22 = k2_yellow_0(X21,X25)
        | r1_lattice3(X21,X25,esk2_3(X21,X22,X25))
        | ~ r1_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r2_yellow_0(X21,X25)
        | r1_lattice3(X21,X25,esk2_3(X21,X22,X25))
        | ~ r1_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( X22 = k2_yellow_0(X21,X25)
        | ~ r1_orders_2(X21,esk2_3(X21,X22,X25),X22)
        | ~ r1_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r2_yellow_0(X21,X25)
        | ~ r1_orders_2(X21,esk2_3(X21,X22,X25),X22)
        | ~ r1_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

fof(c_0_26,plain,(
    ! [X6] :
      ( v2_struct_0(X6)
      | ~ l1_struct_0(X6)
      | ~ v1_xboole_0(u1_struct_0(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( k1_yellow_0(esk3_0,X1) = esk4_0
    | r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,X1))
    | ~ r2_lattice3(esk3_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_29,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk4_0)
    | ~ r3_orders_2(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_21]),c_0_18])]),c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r3_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_21]),c_0_18])]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k1_yellow_0(esk3_0,X1) = esk4_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,X1),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_33,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X3,esk2_3(X2,X1,X3))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk4_0) = k1_tarski(esk4_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(X1)) = esk4_0
    | r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,k1_tarski(X1)))
    | ~ r1_orders_2(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16]),c_0_18])])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_16])])).

cnf(c_0_39,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(X1)) = esk4_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,k1_tarski(X1)),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_16]),c_0_18])])).

cnf(c_0_40,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = esk4_0
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk4_0,X1))
    | ~ r1_lattice3(esk3_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_41,plain,
    ( r1_lattice3(X1,k1_tarski(X3),X2)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = esk4_0
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_43,negated_conjecture,
    ( k1_yellow_0(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) != esk4_0
    | k2_yellow_0(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk4_0) = k1_tarski(esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_22])).

fof(c_0_45,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk4_0)) = esk4_0
    | r2_lattice3(esk3_0,k1_tarski(esk4_0),esk1_3(esk3_0,esk4_0,k1_tarski(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_16])])).

cnf(c_0_48,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk4_0)) = esk4_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,k1_tarski(esk4_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_16])])).

cnf(c_0_49,negated_conjecture,
    ( k2_yellow_0(esk3_0,k1_tarski(X1)) = esk4_0
    | r1_lattice3(esk3_0,k1_tarski(X1),esk2_3(esk3_0,esk4_0,k1_tarski(X1)))
    | ~ r1_orders_2(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_16]),c_0_18])])).

cnf(c_0_50,negated_conjecture,
    ( k2_yellow_0(esk3_0,k1_tarski(X1)) = esk4_0
    | m1_subset_1(esk2_3(esk3_0,esk4_0,k1_tarski(X1)),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_16]),c_0_18])])).

cnf(c_0_51,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk4_0)) != esk4_0
    | k2_yellow_0(esk3_0,k1_tarski(esk4_0)) != esk4_0
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk1_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk4_0)) = esk4_0
    | r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,esk4_0,k1_tarski(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_16]),c_0_18])]),c_0_48])).

cnf(c_0_55,plain,
    ( r1_orders_2(X1,X3,X2)
    | ~ r1_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( k2_yellow_0(esk3_0,k1_tarski(esk4_0)) = esk4_0
    | r1_lattice3(esk3_0,k1_tarski(esk4_0),esk2_3(esk3_0,esk4_0,k1_tarski(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_16])])).

cnf(c_0_57,negated_conjecture,
    ( k2_yellow_0(esk3_0,k1_tarski(esk4_0)) = esk4_0
    | m1_subset_1(esk2_3(esk3_0,esk4_0,k1_tarski(esk4_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_38]),c_0_16])])).

cnf(c_0_58,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk4_0)) != esk4_0
    | k2_yellow_0(esk3_0,k1_tarski(esk4_0)) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_18])])).

cnf(c_0_59,negated_conjecture,
    ( k1_yellow_0(esk3_0,k1_tarski(esk4_0)) = esk4_0
    | ~ r2_lattice3(esk3_0,k1_tarski(esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_17]),c_0_16]),c_0_18])])).

cnf(c_0_60,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,esk2_3(X2,X1,X3),X1)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_61,negated_conjecture,
    ( k2_yellow_0(esk3_0,k1_tarski(esk4_0)) = esk4_0
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,k1_tarski(esk4_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_16]),c_0_18])]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k2_yellow_0(esk3_0,k1_tarski(esk4_0)) != esk4_0
    | ~ r2_lattice3(esk3_0,k1_tarski(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k2_yellow_0(esk3_0,k1_tarski(esk4_0)) = esk4_0
    | ~ r1_lattice3(esk3_0,k1_tarski(esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_17]),c_0_16]),c_0_18])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_lattice3(esk3_0,k1_tarski(esk4_0),esk4_0)
    | ~ r2_lattice3(esk3_0,k1_tarski(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,k1_tarski(esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_41]),c_0_38]),c_0_16]),c_0_18])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_29]),c_0_38]),c_0_16]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
