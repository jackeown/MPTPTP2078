%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1999+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:07 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 (26429 expanded)
%              Number of clauses        :   78 (7804 expanded)
%              Number of leaves         :   15 (6426 expanded)
%              Depth                    :   26
%              Number of atoms          :  534 (390867 expanded)
%              Number of equality atoms :   44 ( 237 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   60 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_waybel_3(X1)
        & l1_orders_2(X1) )
     => ( v5_waybel_7(k1_waybel_4(X1),X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v4_waybel_7(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r1_waybel_3(X1,k12_lattice3(X1,X3,X4),X2)
                          & ~ r3_orders_2(X1,X3,X2)
                          & ~ r3_orders_2(X1,X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_waybel_7)).

fof(l57_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_waybel_3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v5_waybel_7(k1_waybel_4(X1),X1)
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r1_waybel_3(X1,k12_lattice3(X1,X3,X4),X2)
                          & ~ r3_orders_2(X1,X3,X2)
                          & ~ r3_orders_2(X1,X4,X2) ) ) )
              & ~ v5_waybel_6(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_waybel_7)).

fof(t38_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
           => v4_waybel_7(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_7)).

fof(t40_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_yellow_0)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(dt_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(t39_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_waybel_3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v4_waybel_7(X2,X1)
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & v1_finset_1(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
               => ~ ( r1_waybel_3(X1,k2_yellow_0(X1,X3),X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ~ ( r2_hidden(X4,X3)
                            & r3_orders_2(X1,X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_waybel_7)).

fof(fc2_finset_1,axiom,(
    ! [X1,X2] : v1_finset_1(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_finset_1)).

fof(fc3_xboole_0,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

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

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_waybel_3(X1)
          & l1_orders_2(X1) )
       => ( v5_waybel_7(k1_waybel_4(X1),X1)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ( v4_waybel_7(X2,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ~ ( r1_waybel_3(X1,k12_lattice3(X1,X3,X4),X2)
                            & ~ r3_orders_2(X1,X3,X2)
                            & ~ r3_orders_2(X1,X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_waybel_7])).

fof(c_0_16,plain,(
    ! [X24,X25] :
      ( ( m1_subset_1(esk2_2(X24,X25),u1_struct_0(X24))
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) )
      & ( m1_subset_1(esk3_2(X24,X25),u1_struct_0(X24))
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) )
      & ( r1_waybel_3(X24,k12_lattice3(X24,esk2_2(X24,X25),esk3_2(X24,X25)),X25)
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ r3_orders_2(X24,esk2_2(X24,X25),X25)
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ r3_orders_2(X24,esk3_2(X24,X25),X25)
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l57_waybel_7])])])])])])).

fof(c_0_17,negated_conjecture,(
    ! [X45,X46] :
      ( v3_orders_2(esk5_0)
      & v4_orders_2(esk5_0)
      & v5_orders_2(esk5_0)
      & v1_yellow_0(esk5_0)
      & v1_lattice3(esk5_0)
      & v2_lattice3(esk5_0)
      & v3_waybel_3(esk5_0)
      & l1_orders_2(esk5_0)
      & v5_waybel_7(k1_waybel_4(esk5_0),esk5_0)
      & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
      & ( m1_subset_1(esk7_0,u1_struct_0(esk5_0))
        | ~ v4_waybel_7(esk6_0,esk5_0) )
      & ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
        | ~ v4_waybel_7(esk6_0,esk5_0) )
      & ( r1_waybel_3(esk5_0,k12_lattice3(esk5_0,esk7_0,esk8_0),esk6_0)
        | ~ v4_waybel_7(esk6_0,esk5_0) )
      & ( ~ r3_orders_2(esk5_0,esk7_0,esk6_0)
        | ~ v4_waybel_7(esk6_0,esk5_0) )
      & ( ~ r3_orders_2(esk5_0,esk8_0,esk6_0)
        | ~ v4_waybel_7(esk6_0,esk5_0) )
      & ( v4_waybel_7(esk6_0,esk5_0)
        | ~ m1_subset_1(X45,u1_struct_0(esk5_0))
        | ~ m1_subset_1(X46,u1_struct_0(esk5_0))
        | ~ r1_waybel_3(esk5_0,k12_lattice3(esk5_0,X45,X46),esk6_0)
        | r3_orders_2(esk5_0,X45,esk6_0)
        | r3_orders_2(esk5_0,X46,esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

cnf(c_0_18,plain,
    ( r1_waybel_3(X1,k12_lattice3(X1,esk2_2(X1,X2),esk3_2(X1,X2)),X2)
    | v5_waybel_6(X2,X1)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v5_waybel_7(k1_waybel_4(esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v3_waybel_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_yellow_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v5_waybel_6(X2,X1)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v5_waybel_6(X2,X1)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v5_waybel_6(X1,esk5_0)
    | r1_waybel_3(esk5_0,k12_lattice3(esk5_0,esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( v5_waybel_6(X1,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( v5_waybel_6(X1,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_34,plain,
    ( v5_waybel_6(X2,X1)
    | ~ r3_orders_2(X1,esk3_2(X1,X2),X2)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( v4_waybel_7(esk6_0,esk5_0)
    | r3_orders_2(esk5_0,X1,esk6_0)
    | r3_orders_2(esk5_0,X2,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r1_waybel_3(esk5_0,k12_lattice3(esk5_0,X1,X2),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( v5_waybel_6(esk6_0,esk5_0)
    | r1_waybel_3(esk5_0,k12_lattice3(esk5_0,esk2_2(esk5_0,esk6_0),esk3_2(esk5_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v5_waybel_6(esk6_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v5_waybel_6(esk6_0,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_39,plain,
    ( v5_waybel_6(X2,X1)
    | ~ r3_orders_2(X1,esk2_2(X1,X2),X2)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( v5_waybel_6(X1,esk5_0)
    | ~ r3_orders_2(esk5_0,esk3_2(esk5_0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_41,negated_conjecture,
    ( v4_waybel_7(esk6_0,esk5_0)
    | v5_waybel_6(esk6_0,esk5_0)
    | r3_orders_2(esk5_0,esk2_2(esk5_0,esk6_0),esk6_0)
    | r3_orders_2(esk5_0,esk3_2(esk5_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

fof(c_0_42,plain,(
    ! [X31,X32] :
      ( ~ v3_orders_2(X31)
      | ~ v4_orders_2(X31)
      | ~ v5_orders_2(X31)
      | ~ v1_lattice3(X31)
      | ~ v2_lattice3(X31)
      | ~ l1_orders_2(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ v5_waybel_6(X32,X31)
      | v4_waybel_7(X32,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_waybel_7])])])).

cnf(c_0_43,negated_conjecture,
    ( v5_waybel_6(X1,esk5_0)
    | ~ r3_orders_2(esk5_0,esk2_2(esk5_0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_44,negated_conjecture,
    ( v4_waybel_7(esk6_0,esk5_0)
    | v5_waybel_6(esk6_0,esk5_0)
    | r3_orders_2(esk5_0,esk2_2(esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31])])).

cnf(c_0_45,plain,
    ( v4_waybel_7(X2,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_waybel_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( v4_waybel_7(esk6_0,esk5_0)
    | v5_waybel_6(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_31])])).

fof(c_0_47,plain,(
    ! [X37,X38,X39] :
      ( ~ v3_orders_2(X37)
      | ~ v4_orders_2(X37)
      | ~ v5_orders_2(X37)
      | ~ v2_lattice3(X37)
      | ~ l1_orders_2(X37)
      | ~ m1_subset_1(X38,u1_struct_0(X37))
      | ~ m1_subset_1(X39,u1_struct_0(X37))
      | k2_yellow_0(X37,k7_domain_1(u1_struct_0(X37),X38,X39)) = k12_lattice3(X37,X38,X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_yellow_0])])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    | ~ v4_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( v4_waybel_7(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_21]),c_0_23]),c_0_24]),c_0_25]),c_0_31]),c_0_26]),c_0_27])])).

fof(c_0_50,plain,(
    ! [X28,X29,X30] :
      ( v1_xboole_0(X28)
      | ~ m1_subset_1(X29,X28)
      | ~ m1_subset_1(X30,X28)
      | k7_domain_1(X28,X29,X30) = k2_tarski(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

cnf(c_0_51,plain,
    ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    | ~ v4_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k2_yellow_0(esk5_0,k7_domain_1(u1_struct_0(esk5_0),X1,esk8_0)) = k12_lattice3(esk5_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_49])])).

cnf(c_0_57,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk5_0),X1,esk8_0) = k2_tarski(X1,esk8_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_52])).

fof(c_0_58,plain,(
    ! [X15,X16,X17] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(X16,X15)
      | ~ m1_subset_1(X17,X15)
      | m1_subset_1(k7_domain_1(X15,X16,X17),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).

cnf(c_0_59,negated_conjecture,
    ( r1_waybel_3(esk5_0,k12_lattice3(esk5_0,esk7_0,esk8_0),esk6_0)
    | ~ v4_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( k2_yellow_0(esk5_0,k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk8_0)) = k12_lattice3(esk5_0,esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk8_0) = k2_tarski(esk7_0,esk8_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_63,plain,(
    ! [X33,X34,X35] :
      ( ( m1_subset_1(esk4_3(X33,X34,X35),u1_struct_0(X33))
        | ~ r1_waybel_3(X33,k2_yellow_0(X33,X35),X34)
        | v1_xboole_0(X35)
        | ~ v1_finset_1(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v4_waybel_7(X34,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ v1_lattice3(X33)
        | ~ v2_lattice3(X33)
        | ~ v3_waybel_3(X33)
        | ~ l1_orders_2(X33) )
      & ( r2_hidden(esk4_3(X33,X34,X35),X35)
        | ~ r1_waybel_3(X33,k2_yellow_0(X33,X35),X34)
        | v1_xboole_0(X35)
        | ~ v1_finset_1(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v4_waybel_7(X34,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ v1_lattice3(X33)
        | ~ v2_lattice3(X33)
        | ~ v3_waybel_3(X33)
        | ~ l1_orders_2(X33) )
      & ( r3_orders_2(X33,esk4_3(X33,X34,X35),X34)
        | ~ r1_waybel_3(X33,k2_yellow_0(X33,X35),X34)
        | v1_xboole_0(X35)
        | ~ v1_finset_1(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v4_waybel_7(X34,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ v1_lattice3(X33)
        | ~ v2_lattice3(X33)
        | ~ v3_waybel_3(X33)
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_waybel_7])])])])])])).

cnf(c_0_64,negated_conjecture,
    ( r1_waybel_3(esk5_0,k12_lattice3(esk5_0,esk7_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_49])])).

cnf(c_0_65,negated_conjecture,
    ( k12_lattice3(esk5_0,esk7_0,esk8_0) = k2_yellow_0(esk5_0,k2_tarski(esk7_0,esk8_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_66,plain,(
    ! [X19,X20] : v1_finset_1(k2_tarski(X19,X20)) ),
    inference(variable_rename,[status(thm)],[fc2_finset_1])).

fof(c_0_67,plain,(
    ! [X22,X23] : ~ v1_xboole_0(k2_tarski(X22,X23)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k7_domain_1(u1_struct_0(esk5_0),X1,esk8_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_52])).

fof(c_0_69,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_70,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | v1_xboole_0(X3)
    | ~ r1_waybel_3(X1,k2_yellow_0(X1,X3),X2)
    | ~ v1_finset_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_waybel_7(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r1_waybel_3(esk5_0,k2_yellow_0(esk5_0,k2_tarski(esk7_0,esk8_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( v1_finset_1(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k7_domain_1(u1_struct_0(esk5_0),esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_56])).

cnf(c_0_75,plain,
    ( r3_orders_2(X1,esk4_3(X1,X2,X3),X2)
    | v1_xboole_0(X3)
    | ~ r1_waybel_3(X1,k2_yellow_0(X1,X3),X2)
    | ~ v1_finset_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_waybel_7(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_hidden(esk4_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk8_0)),k2_tarski(esk7_0,esk8_0))
    | ~ m1_subset_1(k2_tarski(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_49]),c_0_20]),c_0_21]),c_0_23]),c_0_24]),c_0_25]),c_0_72]),c_0_31]),c_0_26]),c_0_27])]),c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_61])).

cnf(c_0_79,negated_conjecture,
    ( r3_orders_2(esk5_0,esk4_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk8_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(k2_tarski(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_71]),c_0_49]),c_0_20]),c_0_21]),c_0_23]),c_0_24]),c_0_25]),c_0_72]),c_0_31]),c_0_26]),c_0_27])]),c_0_73])).

cnf(c_0_80,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_hidden(esk4_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk8_0)),k2_tarski(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( ~ r3_orders_2(esk5_0,esk8_0,esk6_0)
    | ~ v4_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_83,negated_conjecture,
    ( r3_orders_2(esk5_0,esk4_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk8_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk8_0)) = esk8_0
    | esk4_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk8_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( ~ r3_orders_2(esk5_0,esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_49])])).

cnf(c_0_86,negated_conjecture,
    ( ~ r3_orders_2(esk5_0,esk7_0,esk6_0)
    | ~ v4_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_87,plain,(
    ! [X40] :
      ( ~ v1_xboole_0(X40)
      | X40 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_88,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,k2_tarski(esk7_0,esk8_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( ~ r3_orders_2(esk5_0,esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_49])])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_88]),c_0_89])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_90])).

cnf(c_0_93,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_94])).

fof(c_0_97,plain,(
    ! [X21] :
      ( v2_struct_0(X21)
      | ~ l1_struct_0(X21)
      | ~ v1_xboole_0(u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_98,negated_conjecture,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( u1_struct_0(esk5_0) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_94,c_0_98])).

fof(c_0_101,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_102,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v2_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_103,negated_conjecture,
    ( v2_struct_0(esk5_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_93])])).

cnf(c_0_104,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_105,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( v2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_27])])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_26]),c_0_27])]),
    [proof]).

%------------------------------------------------------------------------------
