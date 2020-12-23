%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:48 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 229 expanded)
%              Number of clauses        :   38 (  92 expanded)
%              Number of leaves         :   14 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  248 ( 639 expanded)
%              Number of equality atoms :   14 ( 119 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

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

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(t44_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_yellow_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & r1_lattice3(X1,u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( r2_hidden(k1_xboole_0,X1)
         => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_1])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( ~ v5_orders_2(X11)
      | ~ l1_orders_2(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | ~ r1_orders_2(X11,X12,X13)
      | ~ r1_orders_2(X11,X13,X12)
      | X12 = X13 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

fof(c_0_16,plain,(
    ! [X26] :
      ( v1_orders_2(k2_yellow_1(X26))
      & v3_orders_2(k2_yellow_1(X26))
      & v4_orders_2(k2_yellow_1(X26))
      & v5_orders_2(k2_yellow_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_17,plain,(
    ! [X25] :
      ( v1_orders_2(k2_yellow_1(X25))
      & l1_orders_2(k2_yellow_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_18,plain,(
    ! [X28] :
      ( u1_struct_0(k2_yellow_1(X28)) = X28
      & u1_orders_2(k2_yellow_1(X28)) = k1_yellow_1(X28) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_19,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | m1_subset_1(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & r2_hidden(k1_xboole_0,esk3_0)
    & k3_yellow_0(k2_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_21,plain,(
    ! [X29,X30,X31] :
      ( ( ~ r3_orders_2(k2_yellow_1(X29),X30,X31)
        | r1_tarski(X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(k2_yellow_1(X29)))
        | ~ m1_subset_1(X30,u1_struct_0(k2_yellow_1(X29)))
        | v1_xboole_0(X29) )
      & ( ~ r1_tarski(X30,X31)
        | r3_orders_2(k2_yellow_1(X29),X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(k2_yellow_1(X29)))
        | ~ m1_subset_1(X30,u1_struct_0(k2_yellow_1(X29)))
        | v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_22,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | m1_subset_1(k3_yellow_0(X22),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

fof(c_0_29,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r3_orders_2(X8,X9,X10)
        | r1_orders_2(X8,X9,X10)
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ l1_orders_2(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8)) )
      & ( ~ r1_orders_2(X8,X9,X10)
        | r3_orders_2(X8,X9,X10)
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ l1_orders_2(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_30,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X27] :
      ( ( ~ v2_struct_0(k2_yellow_1(X27))
        | v1_xboole_0(X27) )
      & ( v1_orders_2(k2_yellow_1(X27))
        | v1_xboole_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r1_orders_2(k2_yellow_1(X3),X2,X1)
    | ~ r1_orders_2(k2_yellow_1(X3),X1,X2)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_25]),c_0_25])).

cnf(c_0_37,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,X1)
    | ~ r1_orders_2(k2_yellow_1(esk3_0),X1,k1_xboole_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_24])])).

cnf(c_0_41,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_42,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v5_orders_2(X23)
      | ~ v1_yellow_0(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | r1_orders_2(X23,k3_yellow_0(X23),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_24]),c_0_37]),c_0_25]),c_0_25])]),c_0_38])).

fof(c_0_44,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_45,plain,(
    ! [X19,X21] :
      ( ( m1_subset_1(esk2_1(X19),u1_struct_0(X19))
        | ~ v1_yellow_0(X19)
        | ~ l1_orders_2(X19) )
      & ( r1_lattice3(X19,u1_struct_0(X19),esk2_1(X19))
        | ~ v1_yellow_0(X19)
        | ~ l1_orders_2(X19) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ r1_lattice3(X19,u1_struct_0(X19),X21)
        | v1_yellow_0(X19)
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_yellow_0])])])])])).

fof(c_0_46,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,X16,esk1_3(X14,X15,X16))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk3_0)))
    | ~ r1_orders_2(k2_yellow_1(esk3_0),k3_yellow_0(k2_yellow_1(esk3_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | r1_orders_2(k2_yellow_1(X1),X2,k3_yellow_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,k3_yellow_0(k2_yellow_1(X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,plain,
    ( v1_yellow_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,u1_struct_0(X2),X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk3_0))
    | ~ v1_yellow_0(k2_yellow_1(esk3_0))
    | ~ r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_23]),c_0_24]),c_0_25]),c_0_33])])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_33]),c_0_50])]),c_0_51])).

cnf(c_0_56,plain,
    ( v1_yellow_0(k2_yellow_1(X1))
    | ~ r1_lattice3(k2_yellow_1(X1),X1,X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_25]),c_0_24])])).

cnf(c_0_57,plain,
    ( r1_lattice3(k2_yellow_1(X1),X2,X3)
    | m1_subset_1(esk1_3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_25]),c_0_24])])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk3_0))
    | ~ v1_yellow_0(k2_yellow_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_59,negated_conjecture,
    ( v1_yellow_0(k2_yellow_1(esk3_0))
    | ~ r1_lattice3(k2_yellow_1(esk3_0),esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_33])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X1)
    | r1_lattice3(k2_yellow_1(X1),X2,X3)
    | r1_orders_2(k2_yellow_1(X1),X4,esk1_3(k2_yellow_1(X1),X2,X3))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(X4,esk1_3(k2_yellow_1(X1),X2,X3)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk3_0))
    | ~ r1_lattice3(k2_yellow_1(esk3_0),esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk3_0),X1,X2)
    | r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,esk1_3(k2_yellow_1(esk3_0),X1,X2))
    | ~ m1_subset_1(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_33]),c_0_50])]),c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_lattice3(k2_yellow_1(esk3_0),esk3_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_61]),c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk3_0),X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_24]),c_0_25]),c_0_33]),c_0_33])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.14/0.39  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t13_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.14/0.39  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_orders_2)).
% 0.14/0.39  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.14/0.39  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.14/0.39  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.14/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.14/0.39  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.14/0.39  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.14/0.39  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.14/0.39  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.14/0.39  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.14/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.39  fof(d4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>(v1_yellow_0(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&r1_lattice3(X1,u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_yellow_0)).
% 0.14/0.39  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.14/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0))), inference(assume_negation,[status(cth)],[t13_yellow_1])).
% 0.14/0.39  fof(c_0_15, plain, ![X11, X12, X13]:(~v5_orders_2(X11)|~l1_orders_2(X11)|(~m1_subset_1(X12,u1_struct_0(X11))|(~m1_subset_1(X13,u1_struct_0(X11))|(~r1_orders_2(X11,X12,X13)|~r1_orders_2(X11,X13,X12)|X12=X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.14/0.39  fof(c_0_16, plain, ![X26]:(((v1_orders_2(k2_yellow_1(X26))&v3_orders_2(k2_yellow_1(X26)))&v4_orders_2(k2_yellow_1(X26)))&v5_orders_2(k2_yellow_1(X26))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.14/0.39  fof(c_0_17, plain, ![X25]:(v1_orders_2(k2_yellow_1(X25))&l1_orders_2(k2_yellow_1(X25))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.14/0.39  fof(c_0_18, plain, ![X28]:(u1_struct_0(k2_yellow_1(X28))=X28&u1_orders_2(k2_yellow_1(X28))=k1_yellow_1(X28)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.14/0.39  fof(c_0_19, plain, ![X6, X7]:(~r2_hidden(X6,X7)|m1_subset_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.14/0.39  fof(c_0_20, negated_conjecture, (~v1_xboole_0(esk3_0)&(r2_hidden(k1_xboole_0,esk3_0)&k3_yellow_0(k2_yellow_1(esk3_0))!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.14/0.39  fof(c_0_21, plain, ![X29, X30, X31]:((~r3_orders_2(k2_yellow_1(X29),X30,X31)|r1_tarski(X30,X31)|~m1_subset_1(X31,u1_struct_0(k2_yellow_1(X29)))|~m1_subset_1(X30,u1_struct_0(k2_yellow_1(X29)))|v1_xboole_0(X29))&(~r1_tarski(X30,X31)|r3_orders_2(k2_yellow_1(X29),X30,X31)|~m1_subset_1(X31,u1_struct_0(k2_yellow_1(X29)))|~m1_subset_1(X30,u1_struct_0(k2_yellow_1(X29)))|v1_xboole_0(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.14/0.39  cnf(c_0_22, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_23, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_24, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_25, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_26, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(k1_xboole_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  fof(c_0_28, plain, ![X22]:(~l1_orders_2(X22)|m1_subset_1(k3_yellow_0(X22),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.14/0.39  fof(c_0_29, plain, ![X8, X9, X10]:((~r3_orders_2(X8,X9,X10)|r1_orders_2(X8,X9,X10)|(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))))&(~r1_orders_2(X8,X9,X10)|r3_orders_2(X8,X9,X10)|(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.14/0.39  cnf(c_0_30, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  fof(c_0_31, plain, ![X27]:((~v2_struct_0(k2_yellow_1(X27))|v1_xboole_0(X27))&(v1_orders_2(k2_yellow_1(X27))|v1_xboole_0(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.14/0.39  cnf(c_0_32, plain, (X1=X2|~r1_orders_2(k2_yellow_1(X3),X2,X1)|~r1_orders_2(k2_yellow_1(X3),X1,X2)|~m1_subset_1(X2,X3)|~m1_subset_1(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_25])])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.39  cnf(c_0_34, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.39  cnf(c_0_35, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.39  cnf(c_0_36, plain, (v1_xboole_0(X1)|r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_25]), c_0_25])).
% 0.14/0.39  cnf(c_0_37, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_38, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (X1=k1_xboole_0|~r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,X1)|~r1_orders_2(k2_yellow_1(esk3_0),X1,k1_xboole_0)|~m1_subset_1(X1,esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.39  cnf(c_0_40, plain, (m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_24])])).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (k3_yellow_0(k2_yellow_1(esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  fof(c_0_42, plain, ![X23, X24]:(v2_struct_0(X23)|~v5_orders_2(X23)|~v1_yellow_0(X23)|~l1_orders_2(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|r1_orders_2(X23,k3_yellow_0(X23),X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.14/0.39  cnf(c_0_43, plain, (v1_xboole_0(X1)|r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_24]), c_0_37]), c_0_25]), c_0_25])]), c_0_38])).
% 0.14/0.39  fof(c_0_44, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.39  fof(c_0_45, plain, ![X19, X21]:(((m1_subset_1(esk2_1(X19),u1_struct_0(X19))|~v1_yellow_0(X19)|~l1_orders_2(X19))&(r1_lattice3(X19,u1_struct_0(X19),esk2_1(X19))|~v1_yellow_0(X19)|~l1_orders_2(X19)))&(~m1_subset_1(X21,u1_struct_0(X19))|~r1_lattice3(X19,u1_struct_0(X19),X21)|v1_yellow_0(X19)|~l1_orders_2(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_yellow_0])])])])])).
% 0.14/0.39  fof(c_0_46, plain, ![X14, X15, X16, X17]:((~r1_lattice3(X14,X15,X16)|(~m1_subset_1(X17,u1_struct_0(X14))|(~r2_hidden(X17,X15)|r1_orders_2(X14,X16,X17)))|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((r2_hidden(esk1_3(X14,X15,X16),X15)|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&(~r1_orders_2(X14,X16,esk1_3(X14,X15,X16))|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (~r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk3_0)))|~r1_orders_2(k2_yellow_1(esk3_0),k3_yellow_0(k2_yellow_1(esk3_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.14/0.39  cnf(c_0_48, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.39  cnf(c_0_49, plain, (v1_xboole_0(X1)|r1_orders_2(k2_yellow_1(X1),X2,k3_yellow_0(k2_yellow_1(X1)))|~m1_subset_1(X2,X1)|~r1_tarski(X2,k3_yellow_0(k2_yellow_1(X1)))), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.14/0.39  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_52, plain, (v1_yellow_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,u1_struct_0(X2),X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.39  cnf(c_0_53, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (v2_struct_0(k2_yellow_1(esk3_0))|~v1_yellow_0(k2_yellow_1(esk3_0))|~r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_23]), c_0_24]), c_0_25]), c_0_33])])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,k3_yellow_0(k2_yellow_1(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_33]), c_0_50])]), c_0_51])).
% 0.14/0.39  cnf(c_0_56, plain, (v1_yellow_0(k2_yellow_1(X1))|~r1_lattice3(k2_yellow_1(X1),X1,X2)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_25]), c_0_24])])).
% 0.14/0.39  cnf(c_0_57, plain, (r1_lattice3(k2_yellow_1(X1),X2,X3)|m1_subset_1(esk1_3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_25]), c_0_24])])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (v2_struct_0(k2_yellow_1(esk3_0))|~v1_yellow_0(k2_yellow_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (v1_yellow_0(k2_yellow_1(esk3_0))|~r1_lattice3(k2_yellow_1(esk3_0),esk3_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_33])).
% 0.14/0.39  cnf(c_0_60, plain, (v1_xboole_0(X1)|r1_lattice3(k2_yellow_1(X1),X2,X3)|r1_orders_2(k2_yellow_1(X1),X4,esk1_3(k2_yellow_1(X1),X2,X3))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~r1_tarski(X4,esk1_3(k2_yellow_1(X1),X2,X3))), inference(spm,[status(thm)],[c_0_43, c_0_57])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, (v2_struct_0(k2_yellow_1(esk3_0))|~r1_lattice3(k2_yellow_1(esk3_0),esk3_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.14/0.39  cnf(c_0_62, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.14/0.39  cnf(c_0_63, negated_conjecture, (r1_lattice3(k2_yellow_1(esk3_0),X1,X2)|r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,esk1_3(k2_yellow_1(esk3_0),X1,X2))|~m1_subset_1(X2,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_33]), c_0_50])]), c_0_51])).
% 0.14/0.39  cnf(c_0_64, negated_conjecture, (~r1_lattice3(k2_yellow_1(esk3_0),esk3_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_61]), c_0_51])).
% 0.14/0.39  cnf(c_0_65, negated_conjecture, (r1_lattice3(k2_yellow_1(esk3_0),X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_24]), c_0_25]), c_0_33]), c_0_33])])).
% 0.14/0.39  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 67
% 0.14/0.39  # Proof object clause steps            : 38
% 0.14/0.39  # Proof object formula steps           : 29
% 0.14/0.39  # Proof object conjectures             : 18
% 0.14/0.39  # Proof object clause conjectures      : 15
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 18
% 0.14/0.39  # Proof object initial formulas used   : 14
% 0.14/0.39  # Proof object generating inferences   : 17
% 0.14/0.39  # Proof object simplifying inferences  : 40
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 14
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 29
% 0.14/0.39  # Removed in clause preprocessing      : 1
% 0.14/0.39  # Initial clauses in saturation        : 28
% 0.14/0.39  # Processed clauses                    : 232
% 0.14/0.39  # ...of these trivial                  : 2
% 0.14/0.39  # ...subsumed                          : 59
% 0.14/0.39  # ...remaining for further processing  : 171
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 6
% 0.14/0.39  # Backward-rewritten                   : 13
% 0.14/0.39  # Generated clauses                    : 288
% 0.14/0.39  # ...of the previous two non-trivial   : 262
% 0.14/0.39  # Contextual simplify-reflections      : 10
% 0.14/0.39  # Paramodulations                      : 288
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
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
% 0.14/0.39  # Current number of processed clauses  : 126
% 0.14/0.39  #    Positive orientable unit clauses  : 13
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 4
% 0.14/0.39  #    Non-unit-clauses                  : 109
% 0.14/0.39  # Current number of unprocessed clauses: 82
% 0.14/0.39  # ...number of literals in the above   : 521
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 46
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 2136
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 486
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 51
% 0.14/0.39  # Unit Clause-clause subsumption calls : 35
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 12
% 0.14/0.39  # BW rewrite match successes           : 4
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 12156
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.048 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.051 s
% 0.14/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
