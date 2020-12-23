%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 225 expanded)
%              Number of clauses        :   34 (  94 expanded)
%              Number of leaves         :   14 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  259 ( 768 expanded)
%              Number of equality atoms :   24 ( 124 expanded)
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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

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
      & ( m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X16)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,esk2_3(X15,X16,X17),X17)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_16,plain,(
    ! [X30] :
      ( u1_struct_0(k2_yellow_1(X30)) = X30
      & u1_orders_2(k2_yellow_1(X30)) = k1_yellow_1(X30) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_17,plain,(
    ! [X27] :
      ( v1_orders_2(k2_yellow_1(X27))
      & l1_orders_2(k2_yellow_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | m1_subset_1(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & r2_hidden(k1_xboole_0,esk4_0)
    & k3_yellow_0(k2_yellow_1(esk4_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
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
        | m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_yellow_0(X21,X25)
        | m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( X22 = k1_yellow_0(X21,X25)
        | r2_lattice3(X21,X25,esk3_3(X21,X22,X25))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_yellow_0(X21,X25)
        | r2_lattice3(X21,X25,esk3_3(X21,X22,X25))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( X22 = k1_yellow_0(X21,X25)
        | ~ r1_orders_2(X21,X22,esk3_3(X21,X22,X25))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_yellow_0(X21,X25)
        | ~ r1_orders_2(X21,X22,esk3_3(X21,X22,X25))
        | ~ r2_lattice3(X21,X25,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_26,plain,(
    ! [X28] :
      ( v1_orders_2(k2_yellow_1(X28))
      & v3_orders_2(k2_yellow_1(X28))
      & v4_orders_2(k2_yellow_1(X28))
      & v5_orders_2(k2_yellow_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_27,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_28,plain,
    ( r2_lattice3(k2_yellow_1(X1),X2,X3)
    | r2_hidden(esk2_3(k2_yellow_1(X1),X2,X3),X2)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk3_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_lattice3(k2_yellow_1(esk4_0),X1,k1_xboole_0)
    | r2_hidden(esk2_3(k2_yellow_1(esk4_0),X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_34,plain,(
    ! [X20] :
      ( ~ l1_orders_2(X20)
      | k3_yellow_0(X20) = k1_yellow_0(X20,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_35,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r3_orders_2(k2_yellow_1(X31),X32,X33)
        | r1_tarski(X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))
        | v1_xboole_0(X31) )
      & ( ~ r1_tarski(X32,X33)
        | r3_orders_2(k2_yellow_1(X31),X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))
        | v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_36,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),X3)
    | m1_subset_1(esk3_3(k2_yellow_1(X2),X1,X3),X2)
    | ~ r2_lattice3(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_21]),c_0_31]),c_0_22])])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(k2_yellow_1(esk4_0),X1,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
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

cnf(c_0_41,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k1_yellow_0(k2_yellow_1(esk4_0),X1) = k1_xboole_0
    | m1_subset_1(esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,X1),esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_44,negated_conjecture,
    ( k1_yellow_0(k2_yellow_1(esk4_0),k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_22])])).

cnf(c_0_45,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_21]),c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_21]),c_0_22]),c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_52,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk4_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_48])])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_55,plain,(
    ! [X29] :
      ( ( ~ v2_struct_0(k2_yellow_1(X29))
        | v1_xboole_0(X29) )
      & ( v1_orders_2(k2_yellow_1(X29))
        | v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_56,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk3_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29])])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk4_0))
    | ~ r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_31]),c_0_22]),c_0_21]),c_0_29])]),c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_37]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.029 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t13_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.13/0.41  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.41  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.13/0.41  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.13/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.41  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.13/0.41  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.13/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.41  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.13/0.41  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.13/0.41  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.13/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.41  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.13/0.41  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0))), inference(assume_negation,[status(cth)],[t13_yellow_1])).
% 0.13/0.41  fof(c_0_15, plain, ![X15, X16, X17, X18]:((~r2_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X16)|r1_orders_2(X15,X18,X17)))|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((r2_hidden(esk2_3(X15,X16,X17),X16)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&(~r1_orders_2(X15,esk2_3(X15,X16,X17),X17)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.41  fof(c_0_16, plain, ![X30]:(u1_struct_0(k2_yellow_1(X30))=X30&u1_orders_2(k2_yellow_1(X30))=k1_yellow_1(X30)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.13/0.41  fof(c_0_17, plain, ![X27]:(v1_orders_2(k2_yellow_1(X27))&l1_orders_2(k2_yellow_1(X27))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.13/0.41  fof(c_0_18, plain, ![X10, X11]:(~r2_hidden(X10,X11)|m1_subset_1(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.41  fof(c_0_19, negated_conjecture, (~v1_xboole_0(esk4_0)&(r2_hidden(k1_xboole_0,esk4_0)&k3_yellow_0(k2_yellow_1(esk4_0))!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.13/0.41  cnf(c_0_20, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_21, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  cnf(c_0_22, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.41  cnf(c_0_23, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.41  cnf(c_0_24, negated_conjecture, (r2_hidden(k1_xboole_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  fof(c_0_25, plain, ![X21, X22, X23, X24, X25]:(((r2_lattice3(X21,X23,X22)|(X22!=k1_yellow_0(X21,X23)|~r1_yellow_0(X21,X23))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_lattice3(X21,X23,X24)|r1_orders_2(X21,X22,X24))|(X22!=k1_yellow_0(X21,X23)|~r1_yellow_0(X21,X23))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))&(((X22=k1_yellow_0(X21,X25)|(m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(r1_yellow_0(X21,X25)|(m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))&(((X22=k1_yellow_0(X21,X25)|(r2_lattice3(X21,X25,esk3_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(r1_yellow_0(X21,X25)|(r2_lattice3(X21,X25,esk3_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))&((X22=k1_yellow_0(X21,X25)|(~r1_orders_2(X21,X22,esk3_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(r1_yellow_0(X21,X25)|(~r1_orders_2(X21,X22,esk3_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.13/0.41  fof(c_0_26, plain, ![X28]:(((v1_orders_2(k2_yellow_1(X28))&v3_orders_2(k2_yellow_1(X28)))&v4_orders_2(k2_yellow_1(X28)))&v5_orders_2(k2_yellow_1(X28))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.13/0.41  fof(c_0_27, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.41  cnf(c_0_28, plain, (r2_lattice3(k2_yellow_1(X1),X2,X3)|r2_hidden(esk2_3(k2_yellow_1(X1),X2,X3),X2)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.41  cnf(c_0_29, negated_conjecture, (m1_subset_1(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.41  cnf(c_0_30, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk3_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.41  cnf(c_0_31, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.41  cnf(c_0_33, negated_conjecture, (r2_lattice3(k2_yellow_1(esk4_0),X1,k1_xboole_0)|r2_hidden(esk2_3(k2_yellow_1(esk4_0),X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.41  fof(c_0_34, plain, ![X20]:(~l1_orders_2(X20)|k3_yellow_0(X20)=k1_yellow_0(X20,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.13/0.41  fof(c_0_35, plain, ![X31, X32, X33]:((~r3_orders_2(k2_yellow_1(X31),X32,X33)|r1_tarski(X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))&(~r1_tarski(X32,X33)|r3_orders_2(k2_yellow_1(X31),X32,X33)|~m1_subset_1(X33,u1_struct_0(k2_yellow_1(X31)))|~m1_subset_1(X32,u1_struct_0(k2_yellow_1(X31)))|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.13/0.41  cnf(c_0_36, plain, (X1=k1_yellow_0(k2_yellow_1(X2),X3)|m1_subset_1(esk3_3(k2_yellow_1(X2),X1,X3),X2)|~r2_lattice3(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_21]), c_0_31]), c_0_22])])).
% 0.13/0.41  cnf(c_0_37, negated_conjecture, (r2_lattice3(k2_yellow_1(esk4_0),X1,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (k3_yellow_0(k2_yellow_1(esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_39, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.41  fof(c_0_40, plain, ![X12, X13, X14]:((~r3_orders_2(X12,X13,X14)|r1_orders_2(X12,X13,X14)|(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))&(~r1_orders_2(X12,X13,X14)|r3_orders_2(X12,X13,X14)|(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.13/0.41  cnf(c_0_41, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.41  cnf(c_0_42, negated_conjecture, (k1_yellow_0(k2_yellow_1(esk4_0),X1)=k1_xboole_0|m1_subset_1(esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,X1),esk4_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29])])).
% 0.13/0.41  cnf(c_0_43, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.41  cnf(c_0_44, negated_conjecture, (k1_yellow_0(k2_yellow_1(esk4_0),k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_22])])).
% 0.13/0.41  cnf(c_0_45, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.41  cnf(c_0_46, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_47, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_21]), c_0_21])).
% 0.13/0.41  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.13/0.41  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_50, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_21]), c_0_22]), c_0_46])])).
% 0.13/0.41  cnf(c_0_51, negated_conjecture, (r3_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|~m1_subset_1(X1,esk4_0)|~r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.13/0.41  fof(c_0_52, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.41  cnf(c_0_53, negated_conjecture, (r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk4_0))|~m1_subset_1(X1,esk4_0)|~r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_48])])).
% 0.13/0.41  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.41  fof(c_0_55, plain, ![X29]:((~v2_struct_0(k2_yellow_1(X29))|v1_xboole_0(X29))&(v1_orders_2(k2_yellow_1(X29))|v1_xboole_0(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.13/0.41  cnf(c_0_56, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk3_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.41  cnf(c_0_57, negated_conjecture, (r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29])])).
% 0.13/0.41  cnf(c_0_58, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.41  cnf(c_0_59, negated_conjecture, (v2_struct_0(k2_yellow_1(esk4_0))|~r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_31]), c_0_22]), c_0_21]), c_0_29])]), c_0_44])).
% 0.13/0.41  cnf(c_0_60, negated_conjecture, (~r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_49])).
% 0.13/0.41  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_37]), c_0_43])]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 62
% 0.13/0.41  # Proof object clause steps            : 34
% 0.13/0.41  # Proof object formula steps           : 28
% 0.13/0.41  # Proof object conjectures             : 18
% 0.13/0.41  # Proof object clause conjectures      : 15
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 18
% 0.13/0.41  # Proof object initial formulas used   : 14
% 0.13/0.41  # Proof object generating inferences   : 15
% 0.13/0.41  # Proof object simplifying inferences  : 29
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 14
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 35
% 0.13/0.41  # Removed in clause preprocessing      : 1
% 0.13/0.41  # Initial clauses in saturation        : 34
% 0.13/0.41  # Processed clauses                    : 253
% 0.13/0.41  # ...of these trivial                  : 4
% 0.13/0.41  # ...subsumed                          : 39
% 0.13/0.41  # ...remaining for further processing  : 210
% 0.13/0.41  # Other redundant clauses eliminated   : 2
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 16
% 0.13/0.41  # Backward-rewritten                   : 6
% 0.13/0.41  # Generated clauses                    : 444
% 0.13/0.41  # ...of the previous two non-trivial   : 408
% 0.13/0.41  # Contextual simplify-reflections      : 32
% 0.13/0.41  # Paramodulations                      : 431
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 2
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 143
% 0.13/0.41  #    Positive orientable unit clauses  : 15
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 4
% 0.13/0.41  #    Non-unit-clauses                  : 124
% 0.13/0.41  # Current number of unprocessed clauses: 206
% 0.13/0.41  # ...number of literals in the above   : 1212
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 66
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 4773
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 912
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 85
% 0.13/0.41  # Unit Clause-clause subsumption calls : 113
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 7
% 0.13/0.41  # BW rewrite match successes           : 3
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 17277
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.053 s
% 0.13/0.41  # System time              : 0.008 s
% 0.13/0.41  # Total time               : 0.062 s
% 0.13/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
