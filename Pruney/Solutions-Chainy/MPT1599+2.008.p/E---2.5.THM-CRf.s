%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:44 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 226 expanded)
%              Number of clauses        :   40 (  93 expanded)
%              Number of leaves         :   11 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 ( 861 expanded)
%              Number of equality atoms :   22 ( 113 expanded)
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

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

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

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

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

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

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

fof(c_0_11,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( r1_orders_2(X18,X21,X19)
        | X21 != k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,X21,X20)
        | X21 != k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X18))
        | ~ r1_orders_2(X18,X22,X19)
        | ~ r1_orders_2(X18,X22,X20)
        | r1_orders_2(X18,X22,X21)
        | X21 != k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk1_4(X18,X19,X20,X21),u1_struct_0(X18))
        | ~ r1_orders_2(X18,X21,X19)
        | ~ r1_orders_2(X18,X21,X20)
        | X21 = k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,esk1_4(X18,X19,X20,X21),X19)
        | ~ r1_orders_2(X18,X21,X19)
        | ~ r1_orders_2(X18,X21,X20)
        | X21 = k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,esk1_4(X18,X19,X20,X21),X20)
        | ~ r1_orders_2(X18,X21,X19)
        | ~ r1_orders_2(X18,X21,X20)
        | X21 = k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ r1_orders_2(X18,esk1_4(X18,X19,X20,X21),X21)
        | ~ r1_orders_2(X18,X21,X19)
        | ~ r1_orders_2(X18,X21,X20)
        | X21 = k11_lattice3(X18,X19,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_lattice3(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_12,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | ~ v2_lattice3(X14)
      | ~ v2_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X26] :
      ( u1_struct_0(k2_yellow_1(X26)) = X26
      & u1_orders_2(k2_yellow_1(X26)) = k1_yellow_1(X26) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_16,plain,(
    ! [X25] :
      ( v1_orders_2(k2_yellow_1(X25))
      & v3_orders_2(k2_yellow_1(X25))
      & v4_orders_2(k2_yellow_1(X25))
      & v5_orders_2(k2_yellow_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_17,plain,(
    ! [X24] :
      ( v1_orders_2(k2_yellow_1(X24))
      & l1_orders_2(k2_yellow_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_18,plain,(
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

cnf(c_0_19,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X15,X16,X17] :
      ( ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | m1_subset_1(k11_lattice3(X15,X16,X17),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

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
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | X2 != k11_lattice3(k2_yellow_1(X1),X4,X3)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v2_lattice3(k2_yellow_1(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_25,c_0_14])).

fof(c_0_32,plain,(
    ! [X9,X10] : k1_setfam_1(k2_tarski(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_33,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_34,plain,(
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

cnf(c_0_35,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_22]),c_0_27])])).

cnf(c_0_36,plain,
    ( r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_22])])).

cnf(c_0_38,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | X2 != k11_lattice3(k2_yellow_1(X1),X3,X4)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( r3_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(k2_yellow_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_38]),c_0_22])])).

cnf(c_0_46,plain,
    ( r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_tarski(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_20]),c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_54,plain,
    ( r3_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_20])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X1)
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_38]),c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X1)
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_59]),c_0_51]),c_0_37])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_58]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:03:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.14/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.029 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 0.14/0.39  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.14/0.39  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.14/0.39  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.14/0.39  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.14/0.39  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.14/0.39  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.14/0.39  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.14/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.39  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.14/0.39  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.14/0.39  fof(c_0_11, plain, ![X18, X19, X20, X21, X22]:((((r1_orders_2(X18,X21,X19)|X21!=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)))&(r1_orders_2(X18,X21,X20)|X21!=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18))))&(~m1_subset_1(X22,u1_struct_0(X18))|(~r1_orders_2(X18,X22,X19)|~r1_orders_2(X18,X22,X20)|r1_orders_2(X18,X22,X21))|X21!=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18))))&((m1_subset_1(esk1_4(X18,X19,X20,X21),u1_struct_0(X18))|(~r1_orders_2(X18,X21,X19)|~r1_orders_2(X18,X21,X20))|X21=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)))&(((r1_orders_2(X18,esk1_4(X18,X19,X20,X21),X19)|(~r1_orders_2(X18,X21,X19)|~r1_orders_2(X18,X21,X20))|X21=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)))&(r1_orders_2(X18,esk1_4(X18,X19,X20,X21),X20)|(~r1_orders_2(X18,X21,X19)|~r1_orders_2(X18,X21,X20))|X21=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18))))&(~r1_orders_2(X18,esk1_4(X18,X19,X20,X21),X21)|(~r1_orders_2(X18,X21,X19)|~r1_orders_2(X18,X21,X20))|X21=k11_lattice3(X18,X19,X20)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_lattice3(X18)|~l1_orders_2(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.14/0.39  fof(c_0_12, plain, ![X14]:(~l1_orders_2(X14)|(~v2_lattice3(X14)|~v2_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.14/0.39  cnf(c_0_13, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_14, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  fof(c_0_15, plain, ![X26]:(u1_struct_0(k2_yellow_1(X26))=X26&u1_orders_2(k2_yellow_1(X26))=k1_yellow_1(X26)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.14/0.39  fof(c_0_16, plain, ![X25]:(((v1_orders_2(k2_yellow_1(X25))&v3_orders_2(k2_yellow_1(X25)))&v4_orders_2(k2_yellow_1(X25)))&v5_orders_2(k2_yellow_1(X25))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.14/0.39  fof(c_0_17, plain, ![X24]:(v1_orders_2(k2_yellow_1(X24))&l1_orders_2(k2_yellow_1(X24))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.14/0.39  fof(c_0_18, plain, ![X11, X12, X13]:((~r3_orders_2(X11,X12,X13)|r1_orders_2(X11,X12,X13)|(v2_struct_0(X11)|~v3_orders_2(X11)|~l1_orders_2(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))))&(~r1_orders_2(X11,X12,X13)|r3_orders_2(X11,X12,X13)|(v2_struct_0(X11)|~v3_orders_2(X11)|~l1_orders_2(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.14/0.39  cnf(c_0_19, plain, (r1_orders_2(X1,X2,X3)|X2!=k11_lattice3(X1,X4,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.39  cnf(c_0_20, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_21, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_22, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  fof(c_0_23, plain, ![X15, X16, X17]:(~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|m1_subset_1(k11_lattice3(X15,X16,X17),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.14/0.39  fof(c_0_24, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.14/0.39  cnf(c_0_25, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X3,X4)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_26, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_27, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_28, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|X2!=k11_lattice3(k2_yellow_1(X1),X4,X3)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.14/0.39  cnf(c_0_29, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  fof(c_0_30, negated_conjecture, (~v1_xboole_0(esk2_0)&(v2_lattice3(k2_yellow_1(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.14/0.39  cnf(c_0_31, plain, (r1_orders_2(X1,X2,X3)|X2!=k11_lattice3(X1,X3,X4)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_25, c_0_14])).
% 0.14/0.39  fof(c_0_32, plain, ![X9, X10]:k1_setfam_1(k2_tarski(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.39  fof(c_0_33, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|r1_tarski(X6,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.14/0.39  fof(c_0_34, plain, ![X27, X28, X29]:((~r3_orders_2(k2_yellow_1(X27),X28,X29)|r1_tarski(X28,X29)|~m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))|~m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))|v1_xboole_0(X27))&(~r1_tarski(X28,X29)|r3_orders_2(k2_yellow_1(X27),X28,X29)|~m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))|~m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))|v1_xboole_0(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.14/0.39  cnf(c_0_35, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_22]), c_0_27])])).
% 0.14/0.39  cnf(c_0_36, plain, (r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.14/0.39  cnf(c_0_37, plain, (m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_20]), c_0_22])])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (v2_lattice3(k2_yellow_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_39, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|X2!=k11_lattice3(k2_yellow_1(X1),X3,X4)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_20]), c_0_21]), c_0_22])])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_41, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  cnf(c_0_42, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.39  cnf(c_0_43, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.39  cnf(c_0_44, plain, (r3_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X3)|v2_struct_0(k2_yellow_1(X1))|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (~v2_struct_0(k2_yellow_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_38]), c_0_22])])).
% 0.14/0.39  cnf(c_0_46, plain, (r1_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_37])).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),k1_setfam_1(k2_tarski(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.39  cnf(c_0_48, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_41])).
% 0.14/0.39  cnf(c_0_49, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_20]), c_0_20])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_45])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_54, plain, (r3_orders_2(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X2)|v2_struct_0(k2_yellow_1(X1))|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_46]), c_0_37])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk4_0)|~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.39  cnf(c_0_56, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X2)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_37])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_52, c_0_20])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_53, c_0_20])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (r3_orders_2(k2_yellow_1(esk2_0),k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X1)|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_38]), c_0_45])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk2_0),X1,X2),X1)|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_59]), c_0_51]), c_0_37])).
% 0.14/0.39  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_58]), c_0_57])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 63
% 0.14/0.39  # Proof object clause steps            : 40
% 0.14/0.39  # Proof object formula steps           : 23
% 0.14/0.39  # Proof object conjectures             : 19
% 0.14/0.39  # Proof object clause conjectures      : 16
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 17
% 0.14/0.39  # Proof object initial formulas used   : 11
% 0.14/0.39  # Proof object generating inferences   : 16
% 0.14/0.39  # Proof object simplifying inferences  : 36
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 11
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 28
% 0.14/0.39  # Removed in clause preprocessing      : 2
% 0.14/0.39  # Initial clauses in saturation        : 26
% 0.14/0.39  # Processed clauses                    : 102
% 0.14/0.39  # ...of these trivial                  : 1
% 0.14/0.39  # ...subsumed                          : 12
% 0.14/0.39  # ...remaining for further processing  : 89
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 1
% 0.14/0.39  # Backward-rewritten                   : 2
% 0.14/0.39  # Generated clauses                    : 192
% 0.14/0.39  # ...of the previous two non-trivial   : 191
% 0.14/0.39  # Contextual simplify-reflections      : 14
% 0.14/0.39  # Paramodulations                      : 183
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 9
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 86
% 0.14/0.39  #    Positive orientable unit clauses  : 9
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 4
% 0.14/0.39  #    Non-unit-clauses                  : 73
% 0.14/0.39  # Current number of unprocessed clauses: 111
% 0.14/0.39  # ...number of literals in the above   : 935
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 5
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1276
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 307
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 26
% 0.14/0.39  # Unit Clause-clause subsumption calls : 8
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 1
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 12206
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.044 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.048 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
