%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t25_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:39 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 470 expanded)
%              Number of clauses        :   35 ( 152 expanded)
%              Number of leaves         :    8 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  283 (3254 expanded)
%              Number of equality atoms :   27 ( 412 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   67 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',reflexivity_r3_orders_2)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',existence_m1_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',t25_yellow_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',redefinition_r3_orders_2)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',cc2_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',t23_yellow_0)).

fof(commutativity_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',commutativity_k12_lattice3)).

fof(dt_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',dt_k12_lattice3)).

fof(c_0_8,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v3_orders_2(X31)
      | ~ l1_orders_2(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | r3_orders_2(X31,X32,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_9,plain,(
    ! [X23] : m1_subset_1(esk6_1(X23),X23) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_10,negated_conjecture,(
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

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v2_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( esk2_0 != k12_lattice3(esk1_0,esk2_0,esk3_0)
      | ~ r3_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( esk2_0 = k12_lattice3(esk1_0,esk2_0,esk3_0)
      | r3_orders_2(esk1_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_14,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r3_orders_2(X28,X29,X30)
        | r1_orders_2(X28,X29,X30)
        | v2_struct_0(X28)
        | ~ v3_orders_2(X28)
        | ~ l1_orders_2(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X28)) )
      & ( ~ r1_orders_2(X28,X29,X30)
        | r3_orders_2(X28,X29,X30)
        | v2_struct_0(X28)
        | ~ v3_orders_2(X28)
        | ~ l1_orders_2(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X49] :
      ( ~ l1_orders_2(X49)
      | ~ v2_lattice3(X49)
      | ~ v2_struct_0(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | r3_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

fof(c_0_22,plain,(
    ! [X36,X37,X38,X39,X40] :
      ( ( r1_orders_2(X36,X39,X37)
        | X39 != k12_lattice3(X36,X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ v5_orders_2(X36)
        | ~ v2_lattice3(X36)
        | ~ l1_orders_2(X36) )
      & ( r1_orders_2(X36,X39,X38)
        | X39 != k12_lattice3(X36,X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ v5_orders_2(X36)
        | ~ v2_lattice3(X36)
        | ~ l1_orders_2(X36) )
      & ( ~ m1_subset_1(X40,u1_struct_0(X36))
        | ~ r1_orders_2(X36,X40,X37)
        | ~ r1_orders_2(X36,X40,X38)
        | r1_orders_2(X36,X40,X39)
        | X39 != k12_lattice3(X36,X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ v5_orders_2(X36)
        | ~ v2_lattice3(X36)
        | ~ l1_orders_2(X36) )
      & ( m1_subset_1(esk7_4(X36,X37,X38,X39),u1_struct_0(X36))
        | ~ r1_orders_2(X36,X39,X37)
        | ~ r1_orders_2(X36,X39,X38)
        | X39 = k12_lattice3(X36,X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ v5_orders_2(X36)
        | ~ v2_lattice3(X36)
        | ~ l1_orders_2(X36) )
      & ( r1_orders_2(X36,esk7_4(X36,X37,X38,X39),X37)
        | ~ r1_orders_2(X36,X39,X37)
        | ~ r1_orders_2(X36,X39,X38)
        | X39 = k12_lattice3(X36,X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ v5_orders_2(X36)
        | ~ v2_lattice3(X36)
        | ~ l1_orders_2(X36) )
      & ( r1_orders_2(X36,esk7_4(X36,X37,X38,X39),X38)
        | ~ r1_orders_2(X36,X39,X37)
        | ~ r1_orders_2(X36,X39,X38)
        | X39 = k12_lattice3(X36,X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ v5_orders_2(X36)
        | ~ v2_lattice3(X36)
        | ~ l1_orders_2(X36) )
      & ( ~ r1_orders_2(X36,esk7_4(X36,X37,X38,X39),X39)
        | ~ r1_orders_2(X36,X39,X37)
        | ~ r1_orders_2(X36,X39,X38)
        | X39 = k12_lattice3(X36,X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ v5_orders_2(X36)
        | ~ v2_lattice3(X36)
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_yellow_0])])])])])).

cnf(c_0_23,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk2_0)
    | v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_26,plain,(
    ! [X11,X12,X13] :
      ( ~ v5_orders_2(X11)
      | ~ v2_lattice3(X11)
      | ~ l1_orders_2(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | k12_lattice3(X11,X12,X13) = k12_lattice3(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).

fof(c_0_27,plain,(
    ! [X17,X18,X19] :
      ( ~ v5_orders_2(X17)
      | ~ v2_lattice3(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | m1_subset_1(k12_lattice3(X17,X18,X19),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).

cnf(c_0_28,plain,
    ( X4 = k12_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk7_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17]),c_0_25])])).

cnf(c_0_30,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 = k12_lattice3(esk1_0,esk2_0,esk3_0)
    | r3_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_orders_2(X1,esk7_4(X1,X2,X3,X4),X3)
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

cnf(c_0_37,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk2_0) = esk2_0
    | ~ r1_orders_2(esk1_0,esk7_4(esk1_0,X1,esk2_0,esk2_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16]),c_0_17]),c_0_25]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( k12_lattice3(esk1_0,esk2_0,esk3_0) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_31]),c_0_32]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_39,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk3_0) = k12_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_17]),c_0_25]),c_0_30])])).

cnf(c_0_40,plain,
    ( r1_orders_2(X1,k12_lattice3(X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk2_0) = esk2_0
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_16]),c_0_17]),c_0_25]),c_0_30])]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k12_lattice3(esk1_0,esk2_0,esk3_0) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_38]),c_0_17]),c_0_25])])).

cnf(c_0_43,negated_conjecture,
    ( k12_lattice3(esk1_0,esk3_0,esk2_0) = k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk1_0,k12_lattice3(esk1_0,esk2_0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_16]),c_0_17]),c_0_25]),c_0_30])])).

cnf(c_0_45,negated_conjecture,
    ( k12_lattice3(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_32])])).

cnf(c_0_46,negated_conjecture,
    ( esk2_0 != k12_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ r3_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_45])])).

cnf(c_0_50,negated_conjecture,
    ( v2_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_32]),c_0_16]),c_0_17]),c_0_18])]),c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_50]),c_0_17]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
