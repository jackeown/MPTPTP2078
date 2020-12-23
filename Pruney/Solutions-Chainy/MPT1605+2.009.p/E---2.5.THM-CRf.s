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
% DateTime   : Thu Dec  3 11:15:47 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 238 expanded)
%              Number of clauses        :   34 (  98 expanded)
%              Number of leaves         :   14 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  259 ( 776 expanded)
%              Number of equality atoms :   23 ( 127 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   50 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

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

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

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

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( r2_hidden(k1_xboole_0,X1)
         => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_1])).

fof(c_0_15,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X16)
        | r1_orders_2(X15,X18,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),u1_struct_0(X15))
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X16)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,esk1_3(X15,X16,X17),X17)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_16,plain,(
    ! [X29] :
      ( u1_struct_0(k2_yellow_1(X29)) = X29
      & u1_orders_2(k2_yellow_1(X29)) = k1_yellow_1(X29) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_17,plain,(
    ! [X27] :
      ( v1_orders_2(k2_yellow_1(X27))
      & l1_orders_2(k2_yellow_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | m1_subset_1(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & r2_hidden(k1_xboole_0,esk3_0)
    & k3_yellow_0(k2_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | ~ r1_tarski(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_21,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( r2_lattice3(X21,X23,X22)
        | X22 != k1_yellow_0(X21,X23)
        | ~ r1_yellow_0(X21,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r2_lattice3(X21,X23,X24)
        | r1_orders_2(X21,X22,X24)
        | X22 != k1_yellow_0(X21,X23)
        | ~ r1_yellow_0(X21,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( X22 = k1_yellow_0(X21,X25)
        | m1_subset_1(esk2_3(X21,X22,X25),u1_struct_0(X21))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_yellow_0(X21,X25)
        | m1_subset_1(esk2_3(X21,X22,X25),u1_struct_0(X21))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( X22 = k1_yellow_0(X21,X25)
        | r2_lattice3(X21,X25,esk2_3(X21,X22,X25))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_yellow_0(X21,X25)
        | r2_lattice3(X21,X25,esk2_3(X21,X22,X25))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( X22 = k1_yellow_0(X21,X25)
        | ~ r1_orders_2(X21,X22,esk2_3(X21,X22,X25))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_yellow_0(X21,X25)
        | ~ r1_orders_2(X21,X22,esk2_3(X21,X22,X25))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_28,plain,(
    ! [X28] :
      ( v1_orders_2(k2_yellow_1(X28))
      & v3_orders_2(k2_yellow_1(X28))
      & v4_orders_2(k2_yellow_1(X28))
      & v5_orders_2(k2_yellow_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_lattice3(k2_yellow_1(X1),X2,X3)
    | r2_hidden(esk1_3(k2_yellow_1(X1),X2,X3),X2)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X20] :
      ( ~ l1_orders_2(X20)
      | k3_yellow_0(X20) = k1_yellow_0(X20,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_34,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r3_orders_2(k2_yellow_1(X30),X31,X32)
        | r1_tarski(X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))
        | v1_xboole_0(X30) )
      & ( ~ r1_tarski(X31,X32)
        | r3_orders_2(k2_yellow_1(X30),X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))
        | ~ m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))
        | v1_xboole_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_35,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(k2_yellow_1(esk3_0),X1,k1_xboole_0)
    | r2_hidden(esk1_3(k2_yellow_1(esk3_0),X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r3_orders_2(X12,X13,X14)
        | r1_orders_2(X12,X13,X14)
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12)) )
      & ( ~ r1_orders_2(X12,X13,X14)
        | r3_orders_2(X12,X13,X14)
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_42,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),X3)
    | m1_subset_1(esk2_3(k2_yellow_1(X2),X1,X3),X2)
    | ~ r2_lattice3(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_23]),c_0_36]),c_0_24])])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k1_yellow_0(k2_yellow_1(esk3_0),k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_24])])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_48,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_23]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32])]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_23]),c_0_47]),c_0_24])])).

cnf(c_0_52,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk3_0),X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

fof(c_0_53,plain,(
    ! [X10] :
      ( ~ v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_54,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk3_0),X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk3_0))
    | ~ m1_subset_1(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_49])])).

cnf(c_0_56,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_30]),c_0_32])])).

cnf(c_0_60,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_36]),c_0_44]),c_0_24]),c_0_23]),c_0_32])]),c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_23]),c_0_24])]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:55:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t13_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.12/0.38  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.12/0.38  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.12/0.38  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.12/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.12/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.38  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.12/0.38  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.12/0.38  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.12/0.38  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.12/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.12/0.38  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.12/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.12/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0))), inference(assume_negation,[status(cth)],[t13_yellow_1])).
% 0.12/0.38  fof(c_0_15, plain, ![X15, X16, X17, X18]:((~r2_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X16)|r1_orders_2(X15,X18,X17)))|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((m1_subset_1(esk1_3(X15,X16,X17),u1_struct_0(X15))|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((r2_hidden(esk1_3(X15,X16,X17),X16)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&(~r1_orders_2(X15,esk1_3(X15,X16,X17),X17)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.12/0.38  fof(c_0_16, plain, ![X29]:(u1_struct_0(k2_yellow_1(X29))=X29&u1_orders_2(k2_yellow_1(X29))=k1_yellow_1(X29)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.12/0.38  fof(c_0_17, plain, ![X27]:(v1_orders_2(k2_yellow_1(X27))&l1_orders_2(k2_yellow_1(X27))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.12/0.38  fof(c_0_18, plain, ![X6, X7]:(~r2_hidden(X6,X7)|m1_subset_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.12/0.38  fof(c_0_19, negated_conjecture, (~v1_xboole_0(esk3_0)&(r2_hidden(k1_xboole_0,esk3_0)&k3_yellow_0(k2_yellow_1(esk3_0))!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.12/0.38  fof(c_0_20, plain, ![X8, X9]:(~r2_hidden(X8,X9)|~r1_tarski(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.38  fof(c_0_21, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.38  cnf(c_0_22, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_23, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_24, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_25, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(k1_xboole_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  fof(c_0_27, plain, ![X21, X22, X23, X24, X25]:(((r2_lattice3(X21,X23,X22)|(X22!=k1_yellow_0(X21,X23)|~r1_yellow_0(X21,X23))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_lattice3(X21,X23,X24)|r1_orders_2(X21,X22,X24))|(X22!=k1_yellow_0(X21,X23)|~r1_yellow_0(X21,X23))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))&(((X22=k1_yellow_0(X21,X25)|(m1_subset_1(esk2_3(X21,X22,X25),u1_struct_0(X21))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(r1_yellow_0(X21,X25)|(m1_subset_1(esk2_3(X21,X22,X25),u1_struct_0(X21))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))&(((X22=k1_yellow_0(X21,X25)|(r2_lattice3(X21,X25,esk2_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(r1_yellow_0(X21,X25)|(r2_lattice3(X21,X25,esk2_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))&((X22=k1_yellow_0(X21,X25)|(~r1_orders_2(X21,X22,esk2_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(r1_yellow_0(X21,X25)|(~r1_orders_2(X21,X22,esk2_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.12/0.38  fof(c_0_28, plain, ![X28]:(((v1_orders_2(k2_yellow_1(X28))&v3_orders_2(k2_yellow_1(X28)))&v4_orders_2(k2_yellow_1(X28)))&v5_orders_2(k2_yellow_1(X28))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.12/0.38  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_30, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_31, plain, (r2_lattice3(k2_yellow_1(X1),X2,X3)|r2_hidden(esk1_3(k2_yellow_1(X1),X2,X3),X2)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.38  fof(c_0_33, plain, ![X20]:(~l1_orders_2(X20)|k3_yellow_0(X20)=k1_yellow_0(X20,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.12/0.38  fof(c_0_34, plain, ![X30, X31, X32]:((~r3_orders_2(k2_yellow_1(X30),X31,X32)|r1_tarski(X31,X32)|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))|~m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))|v1_xboole_0(X30))&(~r1_tarski(X31,X32)|r3_orders_2(k2_yellow_1(X30),X31,X32)|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X30)))|~m1_subset_1(X31,u1_struct_0(k2_yellow_1(X30)))|v1_xboole_0(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.12/0.38  cnf(c_0_35, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_36, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_37, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (r2_lattice3(k2_yellow_1(esk3_0),X1,k1_xboole_0)|r2_hidden(esk1_3(k2_yellow_1(esk3_0),X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (k3_yellow_0(k2_yellow_1(esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_40, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.38  fof(c_0_41, plain, ![X12, X13, X14]:((~r3_orders_2(X12,X13,X14)|r1_orders_2(X12,X13,X14)|(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))&(~r1_orders_2(X12,X13,X14)|r3_orders_2(X12,X13,X14)|(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.12/0.38  cnf(c_0_42, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.38  cnf(c_0_43, plain, (X1=k1_yellow_0(k2_yellow_1(X2),X3)|m1_subset_1(esk2_3(k2_yellow_1(X2),X1,X3),X2)|~r2_lattice3(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_23]), c_0_36]), c_0_24])])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (r2_lattice3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (k1_yellow_0(k2_yellow_1(esk3_0),k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_24])])).
% 0.12/0.38  cnf(c_0_46, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.38  cnf(c_0_47, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_48, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_23]), c_0_23])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_32])]), c_0_45])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_51, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_23]), c_0_47]), c_0_24])])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (r3_orders_2(k2_yellow_1(esk3_0),X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))|~m1_subset_1(X1,esk3_0)|~r1_tarski(X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.12/0.38  fof(c_0_53, plain, ![X10]:(~v2_struct_0(X10)|~l1_struct_0(X10)|v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.12/0.38  fof(c_0_54, plain, ![X11]:(~l1_orders_2(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (r1_orders_2(k2_yellow_1(esk3_0),X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk3_0))|~m1_subset_1(X1,esk3_0)|~r1_tarski(X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_49])])).
% 0.12/0.38  cnf(c_0_56, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.38  cnf(c_0_57, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.12/0.38  cnf(c_0_58, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_30]), c_0_32])])).
% 0.12/0.38  cnf(c_0_60, plain, (v1_xboole_0(u1_struct_0(X1))|~l1_orders_2(X1)|~v2_struct_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (v2_struct_0(k2_yellow_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_36]), c_0_44]), c_0_24]), c_0_23]), c_0_32])]), c_0_45])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_23]), c_0_24])]), c_0_50]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 63
% 0.12/0.38  # Proof object clause steps            : 34
% 0.12/0.38  # Proof object formula steps           : 29
% 0.12/0.38  # Proof object conjectures             : 16
% 0.12/0.38  # Proof object clause conjectures      : 13
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 18
% 0.12/0.38  # Proof object initial formulas used   : 14
% 0.12/0.38  # Proof object generating inferences   : 15
% 0.12/0.38  # Proof object simplifying inferences  : 31
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 14
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 33
% 0.12/0.38  # Removed in clause preprocessing      : 1
% 0.12/0.38  # Initial clauses in saturation        : 32
% 0.12/0.38  # Processed clauses                    : 134
% 0.12/0.38  # ...of these trivial                  : 2
% 0.12/0.38  # ...subsumed                          : 9
% 0.12/0.38  # ...remaining for further processing  : 123
% 0.12/0.38  # Other redundant clauses eliminated   : 2
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 4
% 0.12/0.38  # Backward-rewritten                   : 12
% 0.12/0.38  # Generated clauses                    : 177
% 0.12/0.38  # ...of the previous two non-trivial   : 164
% 0.12/0.38  # Contextual simplify-reflections      : 3
% 0.12/0.38  # Paramodulations                      : 175
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 2
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 74
% 0.12/0.38  #    Positive orientable unit clauses  : 14
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 4
% 0.12/0.38  #    Non-unit-clauses                  : 56
% 0.12/0.38  # Current number of unprocessed clauses: 89
% 0.12/0.38  # ...number of literals in the above   : 530
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 48
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 1316
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 228
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.12/0.38  # Unit Clause-clause subsumption calls : 58
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 3
% 0.12/0.38  # BW rewrite match successes           : 3
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 8775
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.037 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.043 s
% 0.12/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
