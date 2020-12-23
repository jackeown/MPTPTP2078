%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 214 expanded)
%              Number of clauses        :   38 (  87 expanded)
%              Number of leaves         :   10 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  311 ( 846 expanded)
%              Number of equality atoms :   19 ( 107 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   74 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l26_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k10_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

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

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

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

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( r1_orders_2(X16,X17,X19)
        | X19 != k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,X18,X19)
        | X19 != k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X16))
        | ~ r1_orders_2(X16,X17,X20)
        | ~ r1_orders_2(X16,X18,X20)
        | r1_orders_2(X16,X19,X20)
        | X19 != k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk1_4(X16,X17,X18,X19),u1_struct_0(X16))
        | ~ r1_orders_2(X16,X17,X19)
        | ~ r1_orders_2(X16,X18,X19)
        | X19 = k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,X17,esk1_4(X16,X17,X18,X19))
        | ~ r1_orders_2(X16,X17,X19)
        | ~ r1_orders_2(X16,X18,X19)
        | X19 = k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,X18,esk1_4(X16,X17,X18,X19))
        | ~ r1_orders_2(X16,X17,X19)
        | ~ r1_orders_2(X16,X18,X19)
        | X19 = k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,X19,esk1_4(X16,X17,X18,X19))
        | ~ r1_orders_2(X16,X17,X19)
        | ~ r1_orders_2(X16,X18,X19)
        | X19 = k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

fof(c_0_11,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | ~ v1_lattice3(X12)
      | ~ v2_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X24] :
      ( u1_struct_0(k2_yellow_1(X24)) = X24
      & u1_orders_2(k2_yellow_1(X24)) = k1_yellow_1(X24) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_15,plain,(
    ! [X23] :
      ( v1_orders_2(k2_yellow_1(X23))
      & v3_orders_2(k2_yellow_1(X23))
      & v4_orders_2(k2_yellow_1(X23))
      & v5_orders_2(k2_yellow_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_16,plain,(
    ! [X22] :
      ( v1_orders_2(k2_yellow_1(X22))
      & l1_orders_2(k2_yellow_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] :
      ( ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | m1_subset_1(k10_lattice3(X13,X14,X15),u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v1_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_yellow_1])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | X3 != k10_lattice3(k2_yellow_1(X1),X4,X2)
    | ~ v1_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v1_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_24,c_0_13])).

fof(c_0_31,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r3_orders_2(k2_yellow_1(X25),X26,X27)
        | r1_tarski(X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(k2_yellow_1(X25)))
        | ~ m1_subset_1(X26,u1_struct_0(k2_yellow_1(X25)))
        | v1_xboole_0(X25) )
      & ( ~ r1_tarski(X26,X27)
        | r3_orders_2(k2_yellow_1(X25),X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(k2_yellow_1(X25)))
        | ~ m1_subset_1(X26,u1_struct_0(k2_yellow_1(X25)))
        | v1_xboole_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_32,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_21]),c_0_26])])).

cnf(c_0_33,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X3,X2))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(X1),X3,X2),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(k10_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( v1_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | X3 != k10_lattice3(k2_yellow_1(X1),X2,X4)
    | ~ v1_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_20]),c_0_21])])).

fof(c_0_37,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X7)
      | r1_tarski(k2_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X3,X2))
    | v2_struct_0(k2_yellow_1(X1))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_35]),c_0_21])])).

cnf(c_0_41,plain,
    ( r3_orders_2(X1,X2,k10_lattice3(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,k10_lattice3(X1,X3,X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_42,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X3))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_19]),c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),X1,k10_lattice3(k2_yellow_1(esk2_0),X2,X1))
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_50,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X3))
    | v2_struct_0(k2_yellow_1(X1))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_19]),c_0_19]),c_0_21]),c_0_26])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))
    | ~ r1_tarski(esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,k10_lattice3(k2_yellow_1(esk2_0),X2,X1))
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),X1,k10_lattice3(k2_yellow_1(esk2_0),X1,X2))
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_35]),c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,k10_lattice3(k2_yellow_1(esk2_0),X1,X2))
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_55]),c_0_47]),c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_54]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(l26_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k10_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 0.20/0.39  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.20/0.39  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.39  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.20/0.39  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.39  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.39  fof(dt_k10_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 0.20/0.39  fof(t6_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v1_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_1)).
% 0.20/0.39  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.20/0.39  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.20/0.39  fof(c_0_10, plain, ![X16, X17, X18, X19, X20]:((((r1_orders_2(X16,X17,X19)|X19!=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16)))&(r1_orders_2(X16,X18,X19)|X19!=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16))))&(~m1_subset_1(X20,u1_struct_0(X16))|(~r1_orders_2(X16,X17,X20)|~r1_orders_2(X16,X18,X20)|r1_orders_2(X16,X19,X20))|X19!=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16))))&((m1_subset_1(esk1_4(X16,X17,X18,X19),u1_struct_0(X16))|(~r1_orders_2(X16,X17,X19)|~r1_orders_2(X16,X18,X19))|X19=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16)))&(((r1_orders_2(X16,X17,esk1_4(X16,X17,X18,X19))|(~r1_orders_2(X16,X17,X19)|~r1_orders_2(X16,X18,X19))|X19=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16)))&(r1_orders_2(X16,X18,esk1_4(X16,X17,X18,X19))|(~r1_orders_2(X16,X17,X19)|~r1_orders_2(X16,X18,X19))|X19=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16))))&(~r1_orders_2(X16,X19,esk1_4(X16,X17,X18,X19))|(~r1_orders_2(X16,X17,X19)|~r1_orders_2(X16,X18,X19))|X19=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).
% 0.20/0.39  fof(c_0_11, plain, ![X12]:(~l1_orders_2(X12)|(~v1_lattice3(X12)|~v2_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.20/0.39  cnf(c_0_12, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_13, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_14, plain, ![X24]:(u1_struct_0(k2_yellow_1(X24))=X24&u1_orders_2(k2_yellow_1(X24))=k1_yellow_1(X24)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.39  fof(c_0_15, plain, ![X23]:(((v1_orders_2(k2_yellow_1(X23))&v3_orders_2(k2_yellow_1(X23)))&v4_orders_2(k2_yellow_1(X23)))&v5_orders_2(k2_yellow_1(X23))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.20/0.39  fof(c_0_16, plain, ![X22]:(v1_orders_2(k2_yellow_1(X22))&l1_orders_2(k2_yellow_1(X22))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.39  fof(c_0_17, plain, ![X9, X10, X11]:((~r3_orders_2(X9,X10,X11)|r1_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))&(~r1_orders_2(X9,X10,X11)|r3_orders_2(X9,X10,X11)|(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.39  cnf(c_0_18, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X4,X2)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.39  cnf(c_0_19, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_20, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_21, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  fof(c_0_22, plain, ![X13, X14, X15]:(~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))|m1_subset_1(k10_lattice3(X13,X14,X15),u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).
% 0.20/0.39  fof(c_0_23, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v1_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k2_xboole_0(X2,X3),k10_lattice3(k2_yellow_1(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t6_yellow_1])).
% 0.20/0.39  cnf(c_0_24, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_25, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_26, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_27, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|X3!=k10_lattice3(k2_yellow_1(X1),X4,X2)|~v1_lattice3(k2_yellow_1(X1))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.20/0.39  cnf(c_0_28, plain, (m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  fof(c_0_29, negated_conjecture, (~v1_xboole_0(esk2_0)&(v1_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.20/0.39  cnf(c_0_30, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X2,X4)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_24, c_0_13])).
% 0.20/0.39  fof(c_0_31, plain, ![X25, X26, X27]:((~r3_orders_2(k2_yellow_1(X25),X26,X27)|r1_tarski(X26,X27)|~m1_subset_1(X27,u1_struct_0(k2_yellow_1(X25)))|~m1_subset_1(X26,u1_struct_0(k2_yellow_1(X25)))|v1_xboole_0(X25))&(~r1_tarski(X26,X27)|r3_orders_2(k2_yellow_1(X25),X26,X27)|~m1_subset_1(X27,u1_struct_0(k2_yellow_1(X25)))|~m1_subset_1(X26,u1_struct_0(k2_yellow_1(X25)))|v1_xboole_0(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.20/0.39  cnf(c_0_32, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_19]), c_0_21]), c_0_26])])).
% 0.20/0.39  cnf(c_0_33, plain, (r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X3,X2))|~v1_lattice3(k2_yellow_1(X1))|~m1_subset_1(k10_lattice3(k2_yellow_1(X1),X3,X2),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_34, plain, (m1_subset_1(k10_lattice3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_19]), c_0_21])])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (v1_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_36, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|X3!=k10_lattice3(k2_yellow_1(X1),X2,X4)|~v1_lattice3(k2_yellow_1(X1))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_19]), c_0_20]), c_0_21])])).
% 0.20/0.39  fof(c_0_37, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X7)|r1_tarski(k2_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.20/0.39  cnf(c_0_38, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.39  cnf(c_0_39, plain, (r3_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X3,X2))|v2_struct_0(k2_yellow_1(X1))|~v1_lattice3(k2_yellow_1(X1))|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (~v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_35]), c_0_21])])).
% 0.20/0.39  cnf(c_0_41, plain, (r3_orders_2(X1,X2,k10_lattice3(X1,X3,X4))|v2_struct_0(X1)|~r1_orders_2(X1,X2,k10_lattice3(X1,X3,X4))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 0.20/0.39  cnf(c_0_42, plain, (r1_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X3))|~v1_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_34])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (~r1_tarski(k2_xboole_0(esk3_0,esk4_0),k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_44, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_45, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_19]), c_0_19])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),X1,k10_lattice3(k2_yellow_1(esk2_0),X2,X1))|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_35]), c_0_40])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_50, plain, (r3_orders_2(k2_yellow_1(X1),X2,k10_lattice3(k2_yellow_1(X1),X2,X3))|v2_struct_0(k2_yellow_1(X1))|~v1_lattice3(k2_yellow_1(X1))|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_19]), c_0_19]), c_0_21]), c_0_26])])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (~r1_tarski(esk4_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))|~r1_tarski(esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,k10_lattice3(k2_yellow_1(esk2_0),X2,X1))|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_34])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_48, c_0_19])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_49, c_0_19])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),X1,k10_lattice3(k2_yellow_1(esk2_0),X1,X2))|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_35]), c_0_40])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk3_0,k10_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (r1_tarski(X1,k10_lattice3(k2_yellow_1(esk2_0),X1,X2))|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_55]), c_0_47]), c_0_34])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_54]), c_0_53])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 59
% 0.20/0.39  # Proof object clause steps            : 38
% 0.20/0.39  # Proof object formula steps           : 21
% 0.20/0.39  # Proof object conjectures             : 18
% 0.20/0.39  # Proof object clause conjectures      : 15
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 16
% 0.20/0.39  # Proof object initial formulas used   : 10
% 0.20/0.39  # Proof object generating inferences   : 17
% 0.20/0.39  # Proof object simplifying inferences  : 38
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 10
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 27
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 26
% 0.20/0.39  # Processed clauses                    : 110
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 26
% 0.20/0.39  # ...remaining for further processing  : 83
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 2
% 0.20/0.39  # Generated clauses                    : 149
% 0.20/0.39  # ...of the previous two non-trivial   : 148
% 0.20/0.39  # Contextual simplify-reflections      : 14
% 0.20/0.39  # Paramodulations                      : 140
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 9
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 81
% 0.20/0.39  #    Positive orientable unit clauses  : 9
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 68
% 0.20/0.39  # Current number of unprocessed clauses: 64
% 0.20/0.39  # ...number of literals in the above   : 524
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 3
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1154
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 293
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 40
% 0.20/0.39  # Unit Clause-clause subsumption calls : 8
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 1
% 0.20/0.39  # BW rewrite match successes           : 1
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 8718
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.043 s
% 0.20/0.39  # System time              : 0.003 s
% 0.20/0.39  # Total time               : 0.046 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
