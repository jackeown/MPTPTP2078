%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 192 expanded)
%              Number of clauses        :   33 (  77 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  252 ( 663 expanded)
%              Number of equality atoms :   24 ( 118 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

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

fof(t13_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X32] :
      ( u1_struct_0(k2_yellow_1(X32)) = X32
      & u1_orders_2(k2_yellow_1(X32)) = k1_yellow_1(X32) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_16,plain,(
    ! [X30] :
      ( v1_orders_2(k2_yellow_1(X30))
      & v3_orders_2(k2_yellow_1(X30))
      & v4_orders_2(k2_yellow_1(X30))
      & v5_orders_2(k2_yellow_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_17,plain,(
    ! [X29] :
      ( v1_orders_2(k2_yellow_1(X29))
      & l1_orders_2(k2_yellow_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( r2_hidden(k1_xboole_0,X1)
         => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_1])).

cnf(c_0_19,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk3_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

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
    ! [X27,X28] :
      ( ( r2_lattice3(X27,k1_xboole_0,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( r1_lattice3(X27,k1_xboole_0,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_24,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & r2_hidden(k1_xboole_0,esk4_0)
    & k3_yellow_0(k2_yellow_1(esk4_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_26,plain,(
    ! [X20] :
      ( ~ l1_orders_2(X20)
      | k3_yellow_0(X20) = k1_yellow_0(X20,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_27,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r3_orders_2(k2_yellow_1(X33),X34,X35)
        | r1_tarski(X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))
        | v1_xboole_0(X33) )
      & ( ~ r1_tarski(X34,X35)
        | r3_orders_2(k2_yellow_1(X33),X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))
        | v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_28,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),X3)
    | m1_subset_1(esk3_3(k2_yellow_1(X2),X1,X3),X2)
    | ~ r2_lattice3(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_29,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r3_orders_2(X17,X18,X19)
        | r1_orders_2(X17,X18,X19)
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17)) )
      & ( ~ r1_orders_2(X17,X18,X19)
        | r3_orders_2(X17,X18,X19)
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_35,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),k1_xboole_0)
    | m1_subset_1(esk3_3(k2_yellow_1(X2),X1,k1_xboole_0),X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_22]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k1_yellow_0(k2_yellow_1(esk4_0),k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22])])).

cnf(c_0_39,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_20]),c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_44,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_45,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_46,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_22]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk4_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_42])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk4_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_54,plain,(
    ! [X31] :
      ( ( ~ v2_struct_0(k2_yellow_1(X31))
        | v1_xboole_0(X31) )
      & ( v1_orders_2(k2_yellow_1(X31))
        | v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_55,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk3_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_37]),c_0_53])])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk4_0))
    | ~ r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_21]),c_0_22]),c_0_20]),c_0_37])]),c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_22]),c_0_20]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:02:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.13/0.40  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.13/0.40  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.13/0.40  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.13/0.40  fof(t13_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.13/0.40  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.13/0.40  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.40  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.13/0.40  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.13/0.40  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.40  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.13/0.40  fof(c_0_14, plain, ![X21, X22, X23, X24, X25]:(((r2_lattice3(X21,X23,X22)|(X22!=k1_yellow_0(X21,X23)|~r1_yellow_0(X21,X23))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_lattice3(X21,X23,X24)|r1_orders_2(X21,X22,X24))|(X22!=k1_yellow_0(X21,X23)|~r1_yellow_0(X21,X23))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))&(((X22=k1_yellow_0(X21,X25)|(m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(r1_yellow_0(X21,X25)|(m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))&(((X22=k1_yellow_0(X21,X25)|(r2_lattice3(X21,X25,esk3_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(r1_yellow_0(X21,X25)|(r2_lattice3(X21,X25,esk3_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))&((X22=k1_yellow_0(X21,X25)|(~r1_orders_2(X21,X22,esk3_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21)))&(r1_yellow_0(X21,X25)|(~r1_orders_2(X21,X22,esk3_3(X21,X22,X25))|~r2_lattice3(X21,X25,X22))|~m1_subset_1(X22,u1_struct_0(X21))|(~v5_orders_2(X21)|~l1_orders_2(X21))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.13/0.40  fof(c_0_15, plain, ![X32]:(u1_struct_0(k2_yellow_1(X32))=X32&u1_orders_2(k2_yellow_1(X32))=k1_yellow_1(X32)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.13/0.40  fof(c_0_16, plain, ![X30]:(((v1_orders_2(k2_yellow_1(X30))&v3_orders_2(k2_yellow_1(X30)))&v4_orders_2(k2_yellow_1(X30)))&v5_orders_2(k2_yellow_1(X30))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.13/0.40  fof(c_0_17, plain, ![X29]:(v1_orders_2(k2_yellow_1(X29))&l1_orders_2(k2_yellow_1(X29))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.13/0.40  fof(c_0_18, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0))), inference(assume_negation,[status(cth)],[t13_yellow_1])).
% 0.13/0.40  cnf(c_0_19, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk3_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_20, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_21, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_22, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  fof(c_0_23, plain, ![X27, X28]:((r2_lattice3(X27,k1_xboole_0,X28)|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))&(r1_lattice3(X27,k1_xboole_0,X28)|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.13/0.40  fof(c_0_24, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.40  fof(c_0_25, negated_conjecture, (~v1_xboole_0(esk4_0)&(r2_hidden(k1_xboole_0,esk4_0)&k3_yellow_0(k2_yellow_1(esk4_0))!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.13/0.40  fof(c_0_26, plain, ![X20]:(~l1_orders_2(X20)|k3_yellow_0(X20)=k1_yellow_0(X20,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.13/0.40  fof(c_0_27, plain, ![X33, X34, X35]:((~r3_orders_2(k2_yellow_1(X33),X34,X35)|r1_tarski(X34,X35)|~m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))|~m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))|v1_xboole_0(X33))&(~r1_tarski(X34,X35)|r3_orders_2(k2_yellow_1(X33),X34,X35)|~m1_subset_1(X35,u1_struct_0(k2_yellow_1(X33)))|~m1_subset_1(X34,u1_struct_0(k2_yellow_1(X33)))|v1_xboole_0(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.13/0.40  cnf(c_0_28, plain, (X1=k1_yellow_0(k2_yellow_1(X2),X3)|m1_subset_1(esk3_3(k2_yellow_1(X2),X1,X3),X2)|~r2_lattice3(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_29, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_30, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(k1_xboole_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (k3_yellow_0(k2_yellow_1(esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_33, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  fof(c_0_34, plain, ![X17, X18, X19]:((~r3_orders_2(X17,X18,X19)|r1_orders_2(X17,X18,X19)|(v2_struct_0(X17)|~v3_orders_2(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))))&(~r1_orders_2(X17,X18,X19)|r3_orders_2(X17,X18,X19)|(v2_struct_0(X17)|~v3_orders_2(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.13/0.40  cnf(c_0_35, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_36, plain, (X1=k1_yellow_0(k2_yellow_1(X2),k1_xboole_0)|m1_subset_1(esk3_3(k2_yellow_1(X2),X1,k1_xboole_0),X2)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_22]), c_0_20])])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (m1_subset_1(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (k1_yellow_0(k2_yellow_1(esk4_0),k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22])])).
% 0.13/0.40  cnf(c_0_39, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_40, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_41, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_20]), c_0_20])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  fof(c_0_44, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  fof(c_0_45, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  cnf(c_0_46, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_22]), c_0_40])])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (r3_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|~m1_subset_1(X1,esk4_0)|~r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_48, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.40  cnf(c_0_49, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk4_0))|~m1_subset_1(X1,esk4_0)|~r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_42])])).
% 0.13/0.40  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk4_0))|~m1_subset_1(X1,esk4_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.40  cnf(c_0_53, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.40  fof(c_0_54, plain, ![X31]:((~v2_struct_0(k2_yellow_1(X31))|v1_xboole_0(X31))&(v1_orders_2(k2_yellow_1(X31))|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.13/0.40  cnf(c_0_55, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk3_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_37]), c_0_53])])).
% 0.13/0.40  cnf(c_0_57, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (v2_struct_0(k2_yellow_1(esk4_0))|~r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_21]), c_0_22]), c_0_20]), c_0_37])]), c_0_38])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (~r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_43])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_29]), c_0_22]), c_0_20]), c_0_37])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 61
% 0.13/0.40  # Proof object clause steps            : 33
% 0.13/0.40  # Proof object formula steps           : 28
% 0.13/0.40  # Proof object conjectures             : 16
% 0.13/0.40  # Proof object clause conjectures      : 13
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 18
% 0.13/0.40  # Proof object initial formulas used   : 14
% 0.13/0.40  # Proof object generating inferences   : 14
% 0.13/0.40  # Proof object simplifying inferences  : 30
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 14
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 35
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 34
% 0.13/0.40  # Processed clauses                    : 223
% 0.13/0.40  # ...of these trivial                  : 2
% 0.13/0.40  # ...subsumed                          : 19
% 0.13/0.40  # ...remaining for further processing  : 202
% 0.13/0.40  # Other redundant clauses eliminated   : 2
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 13
% 0.13/0.40  # Backward-rewritten                   : 12
% 0.13/0.40  # Generated clauses                    : 361
% 0.13/0.40  # ...of the previous two non-trivial   : 320
% 0.13/0.40  # Contextual simplify-reflections      : 21
% 0.13/0.40  # Paramodulations                      : 359
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 2
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 143
% 0.13/0.40  #    Positive orientable unit clauses  : 15
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 4
% 0.13/0.40  #    Non-unit-clauses                  : 124
% 0.13/0.40  # Current number of unprocessed clauses: 150
% 0.13/0.40  # ...number of literals in the above   : 793
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 58
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 4059
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 1379
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 51
% 0.13/0.40  # Unit Clause-clause subsumption calls : 53
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 7
% 0.13/0.40  # BW rewrite match successes           : 3
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 13987
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.047 s
% 0.13/0.40  # System time              : 0.007 s
% 0.13/0.40  # Total time               : 0.054 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
