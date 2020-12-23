%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:45 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 441 expanded)
%              Number of clauses        :   47 ( 176 expanded)
%              Number of leaves         :   13 ( 118 expanded)
%              Depth                    :   15
%              Number of atoms          :  350 (1564 expanded)
%              Number of equality atoms :   23 ( 245 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   74 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l28_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k11_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(dt_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t7_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v2_lattice3(k2_yellow_1(X1))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

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

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t15_lattice3,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(c_0_13,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( r1_orders_2(X17,X20,X18)
        | X20 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X20,X19)
        | X20 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X21,X18)
        | ~ r1_orders_2(X17,X21,X19)
        | r1_orders_2(X17,X21,X20)
        | X20 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk1_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | X20 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk1_4(X17,X18,X19,X20),X18)
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | X20 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk1_4(X17,X18,X19,X20),X19)
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | X20 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,esk1_4(X17,X18,X19,X20),X20)
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | X20 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v2_lattice3(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] :
      ( ~ v5_orders_2(X14)
      | ~ v2_lattice3(X14)
      | ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k12_lattice3(X14,X15,X16),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).

fof(c_0_15,plain,(
    ! [X23,X24,X25] :
      ( ~ v5_orders_2(X23)
      | ~ v2_lattice3(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | k12_lattice3(X23,X24,X25) = k11_lattice3(X23,X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,plain,(
    ! [X32] :
      ( u1_struct_0(k2_yellow_1(X32)) = X32
      & u1_orders_2(k2_yellow_1(X32)) = k1_yellow_1(X32) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_22,plain,(
    ! [X30] :
      ( v1_orders_2(k2_yellow_1(X30))
      & v3_orders_2(k2_yellow_1(X30))
      & v4_orders_2(k2_yellow_1(X30))
      & v5_orders_2(k2_yellow_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_23,plain,(
    ! [X29] :
      ( v1_orders_2(k2_yellow_1(X29))
      & l1_orders_2(k2_yellow_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v2_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

cnf(c_0_30,plain,
    ( r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_31,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r3_orders_2(X11,X12,X13)
        | r1_orders_2(X11,X12,X13)
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ m1_subset_1(X13,u1_struct_0(X11)) )
      & ( ~ r1_orders_2(X11,X12,X13)
        | r3_orders_2(X11,X12,X13)
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ m1_subset_1(X13,u1_struct_0(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)
    | v2_struct_0(k2_yellow_1(esk2_0))
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_38,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk4_0,X1),X1)
    | v2_struct_0(k2_yellow_1(esk2_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),X1)
    | v2_struct_0(k2_yellow_1(esk2_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

fof(c_0_42,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r3_orders_2(k2_yellow_1(X33),X34,X35)
        | r1_tarski(X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))
        | v1_xboole_0(X33) )
      & ( ~ r1_tarski(X34,X35)
        | r3_orders_2(k2_yellow_1(X33),X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))
        | v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_43,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_28]),c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0)
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_37])).

cnf(c_0_45,plain,
    ( m1_subset_1(k12_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_47,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0)
    | v2_struct_0(k2_yellow_1(esk2_0))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_37])])).

cnf(c_0_49,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_18]),c_0_27]),c_0_26]),c_0_26]),c_0_28])])).

fof(c_0_50,plain,(
    ! [X9,X10] : k1_setfam_1(k2_tarski(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_51,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_52,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | v2_struct_0(k2_yellow_1(esk2_0))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_46]),c_0_36])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_26]),c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0)
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_31]),c_0_37]),c_0_36])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_31]),c_0_36]),c_0_37])])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk2_0))
    | r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_37])]),c_0_55])).

fof(c_0_61,plain,(
    ! [X26,X27,X28] :
      ( ~ v5_orders_2(X26)
      | ~ v2_lattice3(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | k11_lattice3(X26,X27,X28) = k11_lattice3(X26,X28,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_tarski(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk2_0))
    | r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_59]),c_0_36])]),c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk2_0))
    | r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_49]),c_0_31]),c_0_37]),c_0_36])])).

cnf(c_0_66,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_67,plain,(
    ! [X31] :
      ( ( ~ v2_struct_0(k2_yellow_1(X31))
        | v1_xboole_0(X31) )
      & ( v1_orders_2(k2_yellow_1(X31))
        | v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk2_0))
    | r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_49]),c_0_31]),c_0_36]),c_0_37])])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk2_0))
    | r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_31]),c_0_27]),c_0_26]),c_0_37]),c_0_26]),c_0_36]),c_0_28])])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 0.13/0.38  fof(dt_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 0.13/0.38  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.13/0.38  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.13/0.38  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.13/0.38  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.13/0.38  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.13/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.13/0.38  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.13/0.38  fof(t15_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 0.13/0.38  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.13/0.38  fof(c_0_13, plain, ![X17, X18, X19, X20, X21]:((((r1_orders_2(X17,X20,X18)|X20!=k11_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v2_lattice3(X17)|~l1_orders_2(X17)))&(r1_orders_2(X17,X20,X19)|X20!=k11_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v2_lattice3(X17)|~l1_orders_2(X17))))&(~m1_subset_1(X21,u1_struct_0(X17))|(~r1_orders_2(X17,X21,X18)|~r1_orders_2(X17,X21,X19)|r1_orders_2(X17,X21,X20))|X20!=k11_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v2_lattice3(X17)|~l1_orders_2(X17))))&((m1_subset_1(esk1_4(X17,X18,X19,X20),u1_struct_0(X17))|(~r1_orders_2(X17,X20,X18)|~r1_orders_2(X17,X20,X19))|X20=k11_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v2_lattice3(X17)|~l1_orders_2(X17)))&(((r1_orders_2(X17,esk1_4(X17,X18,X19,X20),X18)|(~r1_orders_2(X17,X20,X18)|~r1_orders_2(X17,X20,X19))|X20=k11_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v2_lattice3(X17)|~l1_orders_2(X17)))&(r1_orders_2(X17,esk1_4(X17,X18,X19,X20),X19)|(~r1_orders_2(X17,X20,X18)|~r1_orders_2(X17,X20,X19))|X20=k11_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v2_lattice3(X17)|~l1_orders_2(X17))))&(~r1_orders_2(X17,esk1_4(X17,X18,X19,X20),X20)|(~r1_orders_2(X17,X20,X18)|~r1_orders_2(X17,X20,X19))|X20=k11_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v2_lattice3(X17)|~l1_orders_2(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X14, X15, X16]:(~v5_orders_2(X14)|~v2_lattice3(X14)|~l1_orders_2(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))|m1_subset_1(k12_lattice3(X14,X15,X16),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).
% 0.13/0.38  fof(c_0_15, plain, ![X23, X24, X25]:(~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|k12_lattice3(X23,X24,X25)=k11_lattice3(X23,X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.13/0.38  cnf(c_0_16, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_18, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_19, plain, (r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)|v2_struct_0(X1)|~v2_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_20, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~v2_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  fof(c_0_21, plain, ![X32]:(u1_struct_0(k2_yellow_1(X32))=X32&u1_orders_2(k2_yellow_1(X32))=k1_yellow_1(X32)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.13/0.38  fof(c_0_22, plain, ![X30]:(((v1_orders_2(k2_yellow_1(X30))&v3_orders_2(k2_yellow_1(X30)))&v4_orders_2(k2_yellow_1(X30)))&v5_orders_2(k2_yellow_1(X30))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.13/0.38  fof(c_0_23, plain, ![X29]:(v1_orders_2(k2_yellow_1(X29))&l1_orders_2(k2_yellow_1(X29))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.13/0.38  fof(c_0_24, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.13/0.38  cnf(c_0_25, plain, (r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)|v2_struct_0(X1)|~v2_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  cnf(c_0_26, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_27, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_28, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  fof(c_0_29, negated_conjecture, (~v1_xboole_0(esk2_0)&(v2_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.13/0.38  cnf(c_0_30, plain, (r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)|v2_struct_0(k2_yellow_1(X1))|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (v2_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  fof(c_0_34, plain, ![X11, X12, X13]:((~r3_orders_2(X11,X12,X13)|r1_orders_2(X11,X12,X13)|(v2_struct_0(X11)|~v3_orders_2(X11)|~l1_orders_2(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))))&(~r1_orders_2(X11,X12,X13)|r3_orders_2(X11,X12,X13)|(v2_struct_0(X11)|~v3_orders_2(X11)|~l1_orders_2(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)|v2_struct_0(k2_yellow_1(esk2_0))|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_32, c_0_26])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_33, c_0_26])).
% 0.13/0.38  cnf(c_0_38, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_39, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk4_0,X1),X1)|v2_struct_0(k2_yellow_1(esk2_0))|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,X1),X1)|v2_struct_0(k2_yellow_1(esk2_0))|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 0.13/0.38  fof(c_0_42, plain, ![X33, X34, X35]:((~r3_orders_2(k2_yellow_1(X33),X34,X35)|r1_tarski(X34,X35)|~m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))|~m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))|v1_xboole_0(X33))&(~r1_tarski(X34,X35)|r3_orders_2(k2_yellow_1(X33),X34,X35)|~m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))|~m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))|v1_xboole_0(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.13/0.38  cnf(c_0_43, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_26]), c_0_28]), c_0_39])])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0)|v2_struct_0(k2_yellow_1(esk2_0))), inference(spm,[status(thm)],[c_0_40, c_0_37])).
% 0.13/0.38  cnf(c_0_45, plain, (m1_subset_1(k12_lattice3(k2_yellow_1(X1),X2,X3),X1)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_26]), c_0_27]), c_0_28])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r1_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|v2_struct_0(k2_yellow_1(esk2_0))), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 0.13/0.38  cnf(c_0_47, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0)|v2_struct_0(k2_yellow_1(esk2_0))|~m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_37])])).
% 0.13/0.38  cnf(c_0_49, plain, (m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_18]), c_0_27]), c_0_26]), c_0_26]), c_0_28])])).
% 0.13/0.38  fof(c_0_50, plain, ![X9, X10]:k1_setfam_1(k2_tarski(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_51, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|r1_tarski(X6,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|v2_struct_0(k2_yellow_1(esk2_0))|~m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_46]), c_0_36])])).
% 0.13/0.38  cnf(c_0_53, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_26]), c_0_26])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0)|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_31]), c_0_37]), c_0_36])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_57, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.38  cnf(c_0_58, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_31]), c_0_36]), c_0_37])])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (v2_struct_0(k2_yellow_1(esk2_0))|r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0)|~m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_37])]), c_0_55])).
% 0.13/0.38  fof(c_0_61, plain, ![X26, X27, X28]:(~v5_orders_2(X26)|~v2_lattice3(X26)|~l1_orders_2(X26)|(~m1_subset_1(X27,u1_struct_0(X26))|(~m1_subset_1(X28,u1_struct_0(X26))|k11_lattice3(X26,X27,X28)=k11_lattice3(X26,X28,X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_tarski(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.38  cnf(c_0_63, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_58, c_0_57])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (v2_struct_0(k2_yellow_1(esk2_0))|r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|~m1_subset_1(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_59]), c_0_36])]), c_0_55])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (v2_struct_0(k2_yellow_1(esk2_0))|r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk4_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_49]), c_0_31]), c_0_37]), c_0_36])])).
% 0.13/0.38  cnf(c_0_66, plain, (k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.38  fof(c_0_67, plain, ![X31]:((~v2_struct_0(k2_yellow_1(X31))|v1_xboole_0(X31))&(v1_orders_2(k2_yellow_1(X31))|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (v2_struct_0(k2_yellow_1(esk2_0))|r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_49]), c_0_31]), c_0_36]), c_0_37])])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (v2_struct_0(k2_yellow_1(esk2_0))|r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_31]), c_0_27]), c_0_26]), c_0_37]), c_0_26]), c_0_36]), c_0_28])])).
% 0.13/0.38  cnf(c_0_71, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (v2_struct_0(k2_yellow_1(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_55]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 74
% 0.13/0.38  # Proof object clause steps            : 47
% 0.13/0.38  # Proof object formula steps           : 27
% 0.13/0.38  # Proof object conjectures             : 28
% 0.13/0.38  # Proof object clause conjectures      : 25
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 22
% 0.13/0.38  # Proof object simplifying inferences  : 58
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 31
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 29
% 0.13/0.38  # Processed clauses                    : 147
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 35
% 0.13/0.38  # ...remaining for further processing  : 110
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 7
% 0.13/0.38  # Backward-rewritten                   : 30
% 0.13/0.38  # Generated clauses                    : 152
% 0.13/0.38  # ...of the previous two non-trivial   : 151
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 149
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 43
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 31
% 0.13/0.38  # Current number of unprocessed clauses: 55
% 0.13/0.38  # ...number of literals in the above   : 470
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 66
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1073
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 270
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 46
% 0.13/0.38  # Unit Clause-clause subsumption calls : 7
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 7976
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.038 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.044 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
