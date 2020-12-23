%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t48_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:07 EDT 2019

% Result     : Theorem 277.50s
% Output     : CNFRefutation 277.50s
% Verified   : 
% Statistics : Number of formulae       :   94 (7242 expanded)
%              Number of clauses        :   64 (2026 expanded)
%              Number of leaves         :   15 (1809 expanded)
%              Depth                    :   22
%              Number of atoms          :  527 (105886 expanded)
%              Number of equality atoms :   40 (  66 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   60 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',t48_waybel_7)).

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
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',t38_waybel_7)).

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
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',l57_waybel_7)).

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
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',t40_yellow_0)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',redefinition_k7_domain_1)).

fof(dt_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',dt_k7_domain_1)).

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
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',t39_waybel_7)).

fof(fc2_finset_1,axiom,(
    ! [X1,X2] : v1_finset_1(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',fc2_finset_1)).

fof(fc3_xboole_0,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',fc3_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',d2_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',dt_o_0_0_xboole_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',fc2_struct_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',cc2_lattice3)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t48_waybel_7.p',dt_l1_orders_2)).

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
    ! [X67,X68] :
      ( ~ v3_orders_2(X67)
      | ~ v4_orders_2(X67)
      | ~ v5_orders_2(X67)
      | ~ v1_lattice3(X67)
      | ~ v2_lattice3(X67)
      | ~ l1_orders_2(X67)
      | ~ m1_subset_1(X68,u1_struct_0(X67))
      | ~ v5_waybel_6(X68,X67)
      | v4_waybel_7(X68,X67) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_waybel_7])])])).

fof(c_0_17,negated_conjecture,(
    ! [X9,X10] :
      ( v3_orders_2(esk1_0)
      & v4_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & v1_yellow_0(esk1_0)
      & v1_lattice3(esk1_0)
      & v2_lattice3(esk1_0)
      & v3_waybel_3(esk1_0)
      & l1_orders_2(esk1_0)
      & v5_waybel_7(k1_waybel_4(esk1_0),esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
        | ~ v4_waybel_7(esk2_0,esk1_0) )
      & ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ v4_waybel_7(esk2_0,esk1_0) )
      & ( r1_waybel_3(esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk2_0)
        | ~ v4_waybel_7(esk2_0,esk1_0) )
      & ( ~ r3_orders_2(esk1_0,esk3_0,esk2_0)
        | ~ v4_waybel_7(esk2_0,esk1_0) )
      & ( ~ r3_orders_2(esk1_0,esk4_0,esk2_0)
        | ~ v4_waybel_7(esk2_0,esk1_0) )
      & ( v4_waybel_7(esk2_0,esk1_0)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ m1_subset_1(X10,u1_struct_0(esk1_0))
        | ~ r1_waybel_3(esk1_0,k12_lattice3(esk1_0,X9,X10),esk2_0)
        | r3_orders_2(esk1_0,X9,esk2_0)
        | r3_orders_2(esk1_0,X10,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_18,plain,(
    ! [X47,X48] :
      ( ( m1_subset_1(esk9_2(X47,X48),u1_struct_0(X47))
        | ~ v5_waybel_7(k1_waybel_4(X47),X47)
        | v5_waybel_6(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_yellow_0(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ v3_waybel_3(X47)
        | ~ l1_orders_2(X47) )
      & ( m1_subset_1(esk10_2(X47,X48),u1_struct_0(X47))
        | ~ v5_waybel_7(k1_waybel_4(X47),X47)
        | v5_waybel_6(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_yellow_0(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ v3_waybel_3(X47)
        | ~ l1_orders_2(X47) )
      & ( r1_waybel_3(X47,k12_lattice3(X47,esk9_2(X47,X48),esk10_2(X47,X48)),X48)
        | ~ v5_waybel_7(k1_waybel_4(X47),X47)
        | v5_waybel_6(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_yellow_0(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ v3_waybel_3(X47)
        | ~ l1_orders_2(X47) )
      & ( ~ r3_orders_2(X47,esk9_2(X47,X48),X48)
        | ~ v5_waybel_7(k1_waybel_4(X47),X47)
        | v5_waybel_6(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_yellow_0(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ v3_waybel_3(X47)
        | ~ l1_orders_2(X47) )
      & ( ~ r3_orders_2(X47,esk10_2(X47,X48),X48)
        | ~ v5_waybel_7(k1_waybel_4(X47),X47)
        | v5_waybel_6(X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ v3_orders_2(X47)
        | ~ v4_orders_2(X47)
        | ~ v5_orders_2(X47)
        | ~ v1_yellow_0(X47)
        | ~ v1_lattice3(X47)
        | ~ v2_lattice3(X47)
        | ~ v3_waybel_3(X47)
        | ~ l1_orders_2(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l57_waybel_7])])])])])])).

cnf(c_0_19,plain,
    ( v4_waybel_7(X2,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_waybel_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v4_waybel_7(esk2_0,esk1_0)
    | r3_orders_2(esk1_0,X1,esk2_0)
    | r3_orders_2(esk1_0,X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ r1_waybel_3(esk1_0,k12_lattice3(esk1_0,X1,X2),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r1_waybel_3(X1,k12_lattice3(X1,esk9_2(X1,X2),esk10_2(X1,X2)),X2)
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v5_waybel_7(k1_waybel_4(esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( v3_waybel_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( v1_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( v4_waybel_7(esk2_0,esk1_0)
    | ~ v5_waybel_6(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_33,plain,
    ( v5_waybel_6(X2,X1)
    | ~ r3_orders_2(X1,esk10_2(X1,X2),X2)
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( r3_orders_2(esk1_0,esk10_2(esk1_0,esk2_0),esk2_0)
    | r3_orders_2(esk1_0,esk9_2(esk1_0,esk2_0),esk2_0)
    | v4_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(esk10_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk9_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20]),c_0_29]),c_0_21]),c_0_30]),c_0_22]),c_0_23]),c_0_31]),c_0_24]),c_0_25]),c_0_26])]),c_0_32])).

cnf(c_0_35,plain,
    ( v5_waybel_6(X2,X1)
    | ~ r3_orders_2(X1,esk9_2(X1,X2),X2)
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( r3_orders_2(esk1_0,esk9_2(esk1_0,esk2_0),esk2_0)
    | v4_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(esk10_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk9_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_20]),c_0_29]),c_0_21]),c_0_30]),c_0_22]),c_0_23]),c_0_31]),c_0_24]),c_0_25]),c_0_26])]),c_0_32])).

fof(c_0_37,plain,(
    ! [X75,X76,X77] :
      ( ~ v3_orders_2(X75)
      | ~ v4_orders_2(X75)
      | ~ v5_orders_2(X75)
      | ~ v2_lattice3(X75)
      | ~ l1_orders_2(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | ~ m1_subset_1(X77,u1_struct_0(X75))
      | k2_yellow_0(X75,k7_domain_1(u1_struct_0(X75),X76,X77)) = k12_lattice3(X75,X76,X77) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_yellow_0])])])).

fof(c_0_38,plain,(
    ! [X54,X55,X56] :
      ( v1_xboole_0(X54)
      | ~ m1_subset_1(X55,X54)
      | ~ m1_subset_1(X56,X54)
      | k7_domain_1(X54,X55,X56) = k2_tarski(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

fof(c_0_39,plain,(
    ! [X39,X40,X41] :
      ( v1_xboole_0(X39)
      | ~ m1_subset_1(X40,X39)
      | ~ m1_subset_1(X41,X39)
      | m1_subset_1(k7_domain_1(X39,X40,X41),k1_zfmisc_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).

cnf(c_0_40,negated_conjecture,
    ( v4_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(esk10_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk9_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_20]),c_0_29]),c_0_21]),c_0_30]),c_0_22]),c_0_23]),c_0_31]),c_0_24]),c_0_25]),c_0_26])]),c_0_32])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk10_2(X1,X2),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_42,plain,(
    ! [X69,X70,X71] :
      ( ( m1_subset_1(esk11_3(X69,X70,X71),u1_struct_0(X69))
        | ~ r1_waybel_3(X69,k2_yellow_0(X69,X71),X70)
        | v1_xboole_0(X71)
        | ~ v1_finset_1(X71)
        | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X69)))
        | ~ v4_waybel_7(X70,X69)
        | ~ m1_subset_1(X70,u1_struct_0(X69))
        | ~ v3_orders_2(X69)
        | ~ v4_orders_2(X69)
        | ~ v5_orders_2(X69)
        | ~ v1_lattice3(X69)
        | ~ v2_lattice3(X69)
        | ~ v3_waybel_3(X69)
        | ~ l1_orders_2(X69) )
      & ( r2_hidden(esk11_3(X69,X70,X71),X71)
        | ~ r1_waybel_3(X69,k2_yellow_0(X69,X71),X70)
        | v1_xboole_0(X71)
        | ~ v1_finset_1(X71)
        | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X69)))
        | ~ v4_waybel_7(X70,X69)
        | ~ m1_subset_1(X70,u1_struct_0(X69))
        | ~ v3_orders_2(X69)
        | ~ v4_orders_2(X69)
        | ~ v5_orders_2(X69)
        | ~ v1_lattice3(X69)
        | ~ v2_lattice3(X69)
        | ~ v3_waybel_3(X69)
        | ~ l1_orders_2(X69) )
      & ( r3_orders_2(X69,esk11_3(X69,X70,X71),X70)
        | ~ r1_waybel_3(X69,k2_yellow_0(X69,X71),X70)
        | v1_xboole_0(X71)
        | ~ v1_finset_1(X71)
        | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X69)))
        | ~ v4_waybel_7(X70,X69)
        | ~ m1_subset_1(X70,u1_struct_0(X69))
        | ~ v3_orders_2(X69)
        | ~ v4_orders_2(X69)
        | ~ v5_orders_2(X69)
        | ~ v1_lattice3(X69)
        | ~ v2_lattice3(X69)
        | ~ v3_waybel_3(X69)
        | ~ l1_orders_2(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_waybel_7])])])])])])).

cnf(c_0_43,plain,
    ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_45,plain,(
    ! [X97,X98] : v1_finset_1(k2_tarski(X97,X98)) ),
    inference(variable_rename,[status(thm)],[fc2_finset_1])).

fof(c_0_46,plain,(
    ! [X100,X101] : ~ v1_xboole_0(k2_tarski(X100,X101)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v4_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(esk9_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_20]),c_0_29]),c_0_21]),c_0_30]),c_0_22]),c_0_23]),c_0_31]),c_0_24]),c_0_25]),c_0_26])]),c_0_32])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk9_2(X1,X2),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_50,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X21
        | X24 = X22
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( esk5_3(X26,X27,X28) != X26
        | ~ r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( esk5_3(X26,X27,X28) != X27
        | ~ r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( r2_hidden(esk5_3(X26,X27,X28),X28)
        | esk5_3(X26,X27,X28) = X26
        | esk5_3(X26,X27,X28) = X27
        | X28 = k2_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_51,plain,
    ( r2_hidden(esk11_3(X1,X2,X3),X3)
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k2_yellow_0(X1,k2_tarski(X2,X3)) = k12_lattice3(X1,X2,X3)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( v1_finset_1(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( r1_waybel_3(esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ v4_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( v4_waybel_7(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_20]),c_0_29]),c_0_21]),c_0_30]),c_0_22]),c_0_23]),c_0_31]),c_0_24]),c_0_25]),c_0_26])]),c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | ~ v4_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    | ~ v4_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(esk11_3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4))
    | ~ r1_waybel_3(X1,k12_lattice3(X1,X3,X4),X2)
    | ~ v4_waybel_7(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_waybel_3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),c_0_54]),c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r1_waybel_3(esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_57])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_57])])).

cnf(c_0_65,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk11_3(esk1_0,esk2_0,k2_tarski(esk3_0,esk4_0)),k2_tarski(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_57]),c_0_20]),c_0_63]),c_0_64]),c_0_21]),c_0_30]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ v4_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_68,plain,
    ( r3_orders_2(X1,esk11_3(X1,X2,X3),X2)
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( esk11_3(esk1_0,esk2_0,k2_tarski(esk3_0,esk4_0)) = esk3_0
    | esk11_3(esk1_0,esk2_0,k2_tarski(esk3_0,esk4_0)) = esk4_0
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_57])])).

cnf(c_0_71,negated_conjecture,
    ( esk11_3(esk1_0,esk2_0,k2_tarski(esk3_0,esk4_0)) = esk3_0
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r1_waybel_3(esk1_0,k2_yellow_0(esk1_0,k2_tarski(esk3_0,esk4_0)),esk2_0)
    | ~ m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_53]),c_0_57]),c_0_20]),c_0_21]),c_0_30]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_54]),c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( esk11_3(esk1_0,esk2_0,k2_tarski(esk3_0,esk4_0)) = esk3_0
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_52]),c_0_62]),c_0_63]),c_0_64]),c_0_21]),c_0_22]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ v4_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_74,plain,(
    ! [X84] :
      ( ~ v1_xboole_0(X84)
      | X84 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_75,negated_conjecture,
    ( esk11_3(esk1_0,esk2_0,k2_tarski(esk3_0,esk4_0)) = esk3_0
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_55]),c_0_63]),c_0_64])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_57])])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_78,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r1_waybel_3(esk1_0,k2_yellow_0(esk1_0,k2_tarski(esk3_0,esk4_0)),esk2_0)
    | ~ m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_75]),c_0_53]),c_0_57]),c_0_20]),c_0_21]),c_0_30]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_54]),c_0_76])).

cnf(c_0_80,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_tarski(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_52]),c_0_62]),c_0_63]),c_0_64]),c_0_21]),c_0_22]),c_0_24]),c_0_25]),c_0_26])])).

fof(c_0_82,plain,(
    ! [X99] :
      ( v2_struct_0(X99)
      | ~ l1_struct_0(X99)
      | ~ v1_xboole_0(u1_struct_0(X99)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_83,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_77,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_55]),c_0_63]),c_0_64])])).

fof(c_0_85,plain,(
    ! [X89] :
      ( ~ l1_orders_2(X89)
      | ~ v2_lattice3(X89)
      | ~ v2_struct_0(X89) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_86,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( u1_struct_0(esk1_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_78])])).

fof(c_0_90,plain,(
    ! [X42] :
      ( ~ l1_orders_2(X42)
      | l1_struct_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_91,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_21]),c_0_22])])).

cnf(c_0_92,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
