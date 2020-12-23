%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t3_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:06 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 100 expanded)
%              Number of clauses        :   24 (  36 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :  179 ( 650 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r2_yellow_0(X1,X2)
            & r2_yellow_0(X1,X3) )
         => r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t35_yellow_0)).

fof(t17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t17_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t3_waybel_7)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',redefinition_r3_orders_2)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',dt_k1_yellow_0)).

fof(t34_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r1_yellow_0(X1,X2)
            & r1_yellow_0(X1,X3) )
         => r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t34_yellow_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',cc2_lattice3)).

fof(c_0_7,plain,(
    ! [X33,X34,X35] :
      ( ~ l1_orders_2(X33)
      | ~ r1_tarski(X34,X35)
      | ~ r2_yellow_0(X33,X34)
      | ~ r2_yellow_0(X33,X35)
      | r1_orders_2(X33,k2_yellow_0(X33,X35),k2_yellow_0(X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_yellow_0])])])).

fof(c_0_8,plain,(
    ! [X24,X25] :
      ( ( r1_yellow_0(X24,X25)
        | v2_struct_0(X24)
        | ~ v5_orders_2(X24)
        | ~ v3_lattice3(X24)
        | ~ l1_orders_2(X24) )
      & ( r2_yellow_0(X24,X25)
        | v2_struct_0(X24)
        | ~ v5_orders_2(X24)
        | ~ v3_lattice3(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X18,X19,X20] :
      ( ( ~ r3_orders_2(X18,X19,X20)
        | r1_orders_2(X18,X19,X20)
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18)) )
      & ( ~ r1_orders_2(X18,X19,X20)
        | r3_orders_2(X18,X19,X20)
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ~ l1_orders_2(X9)
      | m1_subset_1(k1_yellow_0(X9,X10),u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_12,plain,(
    ! [X30,X31,X32] :
      ( ~ l1_orders_2(X30)
      | ~ r1_tarski(X31,X32)
      | ~ r1_yellow_0(X30,X31)
      | ~ r1_yellow_0(X30,X32)
      | r1_orders_2(X30,k1_yellow_0(X30,X31),k1_yellow_0(X30,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_lattice3(esk1_0)
    & v2_lattice3(esk1_0)
    & v3_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & ( ~ r3_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk3_0))
      | ~ r1_orders_2(esk1_0,k2_yellow_0(esk1_0,esk3_0),k2_yellow_0(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_16,plain,(
    ! [X49] :
      ( ~ l1_orders_2(X49)
      | ~ v2_lattice3(X49)
      | ~ v2_struct_0(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_17,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k2_yellow_0(X1,X2),k2_yellow_0(X1,X3))
    | ~ r1_tarski(X3,X2)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,k1_yellow_0(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ r1_tarski(X2,X3)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk3_0))
    | ~ r1_orders_2(esk1_0,k2_yellow_0(esk1_0,esk3_0),k2_yellow_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k2_yellow_0(X1,esk3_0),k2_yellow_0(X1,esk2_0))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v3_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k1_yellow_0(X1,esk2_0),k1_yellow_0(X1,esk3_0))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,k1_yellow_0(X1,esk2_0),k1_yellow_0(X1,esk3_0))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_25]),c_0_30]),c_0_31]),c_0_37])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
