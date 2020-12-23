%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1583+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:26 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 (24461 expanded)
%              Number of clauses        :   91 (9030 expanded)
%              Number of leaves         :   10 (5685 expanded)
%              Depth                    :   38
%              Number of atoms          :  400 (202383 expanded)
%              Number of equality atoms :   10 (13631 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3,X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X2))
                 => ( X5 = X4
                   => ( ( r1_lattice3(X1,X3,X4)
                       => r1_lattice3(X2,X3,X5) )
                      & ( r2_lattice3(X1,X3,X4)
                       => r2_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t59_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_yellow_0)).

fof(t61_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( X5 = X3
                              & X6 = X4
                              & r1_orders_2(X1,X3,X4)
                              & r2_hidden(X5,u1_struct_0(X2)) )
                           => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3,X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X2))
                   => ( X5 = X4
                     => ( ( r1_lattice3(X1,X3,X4)
                         => r1_lattice3(X2,X3,X5) )
                        & ( r2_lattice3(X1,X3,X4)
                         => r2_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_yellow_0])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_orders_2(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v4_yellow_0(esk4_0,esk3_0)
    & m1_yellow_0(esk4_0,esk3_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & esk7_0 = esk6_0
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
      | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( ~ l1_orders_2(X18)
      | ~ m1_yellow_0(X19,X18)
      | l1_orders_2(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

fof(c_0_13,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X13)
        | r1_orders_2(X12,X15,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))
        | r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,esk2_3(X12,X13,X14),X14)
        | r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( esk7_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_yellow_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_23,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_hidden(X10,X8)
        | r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))
        | r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X9,esk1_3(X7,X8,X9))
        | r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_15]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_22])])).

fof(c_0_30,plain,(
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ l1_orders_2(X25)
      | v2_struct_0(X26)
      | ~ m1_yellow_0(X26,X25)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | m1_subset_1(X27,u1_struct_0(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_yellow_0])])])])).

fof(c_0_34,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ~ l1_orders_2(X28)
      | ~ v4_yellow_0(X29,X28)
      | ~ m1_yellow_0(X29,X28)
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ m1_subset_1(X31,u1_struct_0(X28))
      | ~ m1_subset_1(X32,u1_struct_0(X29))
      | ~ m1_subset_1(X33,u1_struct_0(X29))
      | X32 != X30
      | X33 != X31
      | ~ r1_orders_2(X28,X30,X31)
      | ~ r2_hidden(X32,u1_struct_0(X29))
      | r1_orders_2(X29,X32,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_yellow_0])])])).

fof(c_0_35,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | m1_subset_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_39,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_orders_2(X2,X5,X6)
    | ~ l1_orders_2(X1)
    | ~ v4_yellow_0(X2,X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | X5 != X3
    | X6 != X4
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r2_hidden(X5,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_44,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(X1))
    | ~ m1_yellow_0(esk4_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ v4_yellow_0(X1,X4)
    | ~ m1_yellow_0(X1,X4)
    | ~ r1_orders_2(X4,X2,X3)
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_41,c_0_42])])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_22])])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_17]),c_0_18])]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ v4_yellow_0(esk4_0,X2)
    | ~ m1_yellow_0(esk4_0,X2)
    | ~ r1_orders_2(X2,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | ~ m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( v4_yellow_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_18])])).

cnf(c_0_56,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_17]),c_0_18])]),c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_61,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_21]),c_0_22])])).

cnf(c_0_62,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_21]),c_0_57])])).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_21]),c_0_22])])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_66]),c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_67]),c_0_38])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(X1))
    | ~ m1_yellow_0(esk4_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_68]),c_0_38])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_44]),c_0_22])])).

cnf(c_0_73,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_17]),c_0_18])]),c_0_46])).

cnf(c_0_75,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_15])).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,X1)
    | ~ v4_yellow_0(esk4_0,X2)
    | ~ m1_yellow_0(esk4_0,X2)
    | ~ r1_orders_2(X2,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk6_0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk4_0,esk5_0,esk6_0))
    | ~ r2_hidden(esk1_3(esk4_0,esk5_0,esk6_0),X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_18])])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_25])).

cnf(c_0_79,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_80,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r1_orders_2(esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_54]),c_0_17]),c_0_57]),c_0_18])])).

cnf(c_0_81,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk1_3(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_57])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)
    | r1_lattice3(esk4_0,X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_21]),c_0_22])])).

cnf(c_0_83,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_84,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0))
    | ~ r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_68]),c_0_74])])).

cnf(c_0_85,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_28])).

cnf(c_0_86,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_21]),c_0_22])])).

cnf(c_0_87,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_28])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_89]),c_0_38])).

cnf(c_0_91,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(X1))
    | ~ m1_yellow_0(esk4_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_88]),c_0_38])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_44]),c_0_22])])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_17]),c_0_18])]),c_0_46])).

cnf(c_0_94,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | ~ v4_yellow_0(esk4_0,X2)
    | ~ m1_yellow_0(esk4_0,X2)
    | ~ r1_orders_2(X2,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | ~ m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_93]),c_0_18])])).

cnf(c_0_96,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | ~ r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_54]),c_0_17]),c_0_93]),c_0_18])])).

cnf(c_0_98,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_57])])).

cnf(c_0_99,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | ~ r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_21]),c_0_57])])).

cnf(c_0_100,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_61]),c_0_75])).

cnf(c_0_101,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_102,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_101]),c_0_75])).

cnf(c_0_103,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0))
    | ~ r2_hidden(esk1_3(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_102]),c_0_57])])).

cnf(c_0_104,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0))
    | r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_82])).

cnf(c_0_105,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_104]),c_0_86])).

cnf(c_0_106,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_105])])).

cnf(c_0_107,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | ~ r2_hidden(esk2_3(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_106]),c_0_57])])).

cnf(c_0_108,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_105])])).

cnf(c_0_109,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_61]),c_0_108])).

cnf(c_0_110,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_109])])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_110]),c_0_108]),
    [proof]).

%------------------------------------------------------------------------------
