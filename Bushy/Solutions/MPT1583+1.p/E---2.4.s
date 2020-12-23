%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t62_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:46 EDT 2019

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   91 (1346 expanded)
%              Number of clauses        :   68 ( 496 expanded)
%              Number of leaves         :   11 ( 317 expanded)
%              Depth                    :   18
%              Number of atoms          :  352 (10957 expanded)
%              Number of equality atoms :   10 ( 718 expanded)
%              Maximal formula depth    :   19 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t62_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t2_subset)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',dt_m1_yellow_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',fc2_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',d9_lattice3)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',dt_l1_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t59_yellow_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t7_boole)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',d8_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t61_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t1_subset)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_yellow_0(esk2_0,esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & esk5_0 = esk4_0
    & ( r2_lattice3(esk1_0,esk3_0,esk4_0)
      | r1_lattice3(esk1_0,esk3_0,esk4_0) )
    & ( ~ r2_lattice3(esk2_0,esk3_0,esk5_0)
      | r1_lattice3(esk1_0,esk3_0,esk4_0) )
    & ( r2_lattice3(esk1_0,esk3_0,esk4_0)
      | ~ r1_lattice3(esk2_0,esk3_0,esk5_0) )
    & ( ~ r2_lattice3(esk2_0,esk3_0,esk5_0)
      | ~ r1_lattice3(esk2_0,esk3_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_13,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X35,X36)
      | v1_xboole_0(X36)
      | r2_hidden(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X25,X26] :
      ( ~ l1_orders_2(X25)
      | ~ m1_yellow_0(X26,X25)
      | l1_orders_2(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

fof(c_0_17,plain,(
    ! [X51] :
      ( v2_struct_0(X51)
      | ~ l1_struct_0(X51)
      | ~ v1_xboole_0(u1_struct_0(X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r2_hidden(X22,X20)
        | r1_orders_2(X19,X22,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( m1_subset_1(esk7_3(X19,X20,X21),u1_struct_0(X19))
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( r2_hidden(esk7_3(X19,X20,X21),X20)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r1_orders_2(X19,esk7_3(X19,X20,X21),X21)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_21,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_27,plain,(
    ! [X24] :
      ( ~ l1_orders_2(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_28,plain,(
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ l1_orders_2(X37)
      | v2_struct_0(X38)
      | ~ m1_yellow_0(X38,X37)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | m1_subset_1(X39,u1_struct_0(X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_yellow_0])])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

fof(c_0_31,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(X47,X48)
      | ~ v1_xboole_0(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | m1_subset_1(esk7_3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_19]),c_0_30])])).

fof(c_0_36,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk6_3(X14,X15,X16),u1_struct_0(X14))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk6_3(X14,X15,X16),X15)
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,X16,esk6_3(X14,X15,X16))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_37,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ~ l1_orders_2(X40)
      | ~ v4_yellow_0(X41,X40)
      | ~ m1_yellow_0(X41,X40)
      | ~ m1_subset_1(X42,u1_struct_0(X40))
      | ~ m1_subset_1(X43,u1_struct_0(X40))
      | ~ m1_subset_1(X44,u1_struct_0(X41))
      | ~ m1_subset_1(X45,u1_struct_0(X41))
      | X44 != X42
      | X45 != X43
      | ~ r1_orders_2(X40,X42,X43)
      | ~ r2_hidden(X44,u1_struct_0(X41))
      | r1_orders_2(X41,X44,X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_yellow_0])])])).

fof(c_0_38,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | m1_subset_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_30])])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | m1_subset_1(esk7_3(esk2_0,X1,esk4_0),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ m1_yellow_0(esk2_0,X2)
    | ~ l1_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | m1_subset_1(esk7_3(esk2_0,X1,esk4_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_23])]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk4_0)
    | m1_subset_1(esk6_3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_19]),c_0_30])])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X4,X2,X3)
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_yellow_0(X1,X4)
    | ~ v4_yellow_0(X1,X4)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_44,c_0_45])])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk7_3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))
    | r2_lattice3(esk2_0,X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_35]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk2_0,X1,esk4_0),X2)
    | r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_hidden(esk7_3(esk2_0,X1,esk4_0),X3)
    | ~ r2_lattice3(esk1_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_23])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk4_0)
    | m1_subset_1(esk6_3(esk2_0,X1,esk4_0),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ m1_yellow_0(esk2_0,X2)
    | ~ l1_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_49]),c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,X1)
    | ~ r1_orders_2(X2,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk4_0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_yellow_0(esk2_0,X2)
    | ~ v4_yellow_0(esk2_0,X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( v4_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk6_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_3(esk2_0,X1,esk4_0),X2)
    | r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(X3,esk7_3(esk2_0,X1,esk4_0),X2)
    | ~ m1_subset_1(esk7_3(esk2_0,X1,esk4_0),u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_yellow_0(esk2_0,X3)
    | ~ v4_yellow_0(esk2_0,X3)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk2_0,X1,esk4_0),esk4_0)
    | r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_hidden(esk7_3(esk2_0,X1,esk4_0),X2)
    | ~ r2_lattice3(esk1_0,X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_62,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_64,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk4_0)
    | m1_subset_1(esk6_3(esk2_0,X1,esk4_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_23])]),c_0_42])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,X1)
    | ~ r1_orders_2(esk1_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_53]),c_0_56]),c_0_23])])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk6_3(esk2_0,X1,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_19]),c_0_30])])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_3(esk2_0,X1,esk4_0),X2)
    | r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk7_3(esk2_0,X1,esk4_0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_22]),c_0_56]),c_0_23])]),c_0_48])).

cnf(c_0_69,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,esk7_3(esk2_0,X1,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_19]),c_0_30])])).

cnf(c_0_70,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk2_0,X1,esk4_0),esk4_0)
    | r2_lattice3(esk2_0,X1,esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk7_3(esk2_0,X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk7_3(esk2_0,X1,esk4_0),X1)
    | r2_lattice3(esk2_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_19]),c_0_30])])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk6_3(esk2_0,X2,esk4_0))
    | r1_lattice3(esk2_0,X2,esk4_0)
    | ~ r2_hidden(esk6_3(esk2_0,X2,esk4_0),X3)
    | ~ r1_lattice3(esk1_0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_23])])).

cnf(c_0_74,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk6_3(esk2_0,X1,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_49]),c_0_65]),c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk7_3(esk2_0,X1,esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_19]),c_0_53])]),c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk2_0,esk3_0,esk4_0),esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_hidden(esk6_3(esk2_0,X1,esk4_0),X2)
    | ~ r1_lattice3(esk1_0,X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_53]),c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_72])).

cnf(c_0_79,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_80,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_hidden(esk6_3(esk2_0,X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk6_3(esk2_0,X1,esk4_0),X1)
    | r1_lattice3(esk2_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_19]),c_0_30])])).

cnf(c_0_83,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_80,c_0_15])).

cnf(c_0_84,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_lattice3(esk2_0,esk3_0,esk5_0)
    | ~ r1_lattice3(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_86,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_15]),c_0_15])).

cnf(c_0_88,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_hidden(esk7_3(esk2_0,X1,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_86]),c_0_75])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_84])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_71]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
