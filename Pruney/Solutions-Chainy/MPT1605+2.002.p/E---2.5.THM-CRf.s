%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:46 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 202 expanded)
%              Number of clauses        :   35 (  81 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  261 ( 682 expanded)
%              Number of equality atoms :   24 ( 123 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t13_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_15,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( r2_lattice3(X23,X25,X24)
        | X24 != k1_yellow_0(X23,X25)
        | ~ r1_yellow_0(X23,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r2_lattice3(X23,X25,X26)
        | r1_orders_2(X23,X24,X26)
        | X24 != k1_yellow_0(X23,X25)
        | ~ r1_yellow_0(X23,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) )
      & ( X24 = k1_yellow_0(X23,X27)
        | m1_subset_1(esk3_3(X23,X24,X27),u1_struct_0(X23))
        | ~ r2_lattice3(X23,X27,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_yellow_0(X23,X27)
        | m1_subset_1(esk3_3(X23,X24,X27),u1_struct_0(X23))
        | ~ r2_lattice3(X23,X27,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) )
      & ( X24 = k1_yellow_0(X23,X27)
        | r2_lattice3(X23,X27,esk3_3(X23,X24,X27))
        | ~ r2_lattice3(X23,X27,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_yellow_0(X23,X27)
        | r2_lattice3(X23,X27,esk3_3(X23,X24,X27))
        | ~ r2_lattice3(X23,X27,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) )
      & ( X24 = k1_yellow_0(X23,X27)
        | ~ r1_orders_2(X23,X24,esk3_3(X23,X24,X27))
        | ~ r2_lattice3(X23,X27,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_yellow_0(X23,X27)
        | ~ r1_orders_2(X23,X24,esk3_3(X23,X24,X27))
        | ~ r2_lattice3(X23,X27,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_16,plain,(
    ! [X33] :
      ( u1_struct_0(k2_yellow_1(X33)) = X33
      & u1_orders_2(k2_yellow_1(X33)) = k1_yellow_1(X33) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_17,plain,(
    ! [X32] :
      ( v1_orders_2(k2_yellow_1(X32))
      & v3_orders_2(k2_yellow_1(X32))
      & v4_orders_2(k2_yellow_1(X32))
      & v5_orders_2(k2_yellow_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_18,plain,(
    ! [X31] :
      ( v1_orders_2(k2_yellow_1(X31))
      & l1_orders_2(k2_yellow_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( r2_hidden(k1_xboole_0,X1)
         => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_1])).

cnf(c_0_20,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk3_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X29,X30] :
      ( ( r2_lattice3(X29,k1_xboole_0,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ l1_orders_2(X29) )
      & ( r1_lattice3(X29,k1_xboole_0,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & r2_hidden(k1_xboole_0,esk4_0)
    & k3_yellow_0(k2_yellow_1(esk4_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_27,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | k3_yellow_0(X22) = k1_yellow_0(X22,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_28,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r3_orders_2(k2_yellow_1(X34),X35,X36)
        | r1_tarski(X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(k2_yellow_1(X34)))
        | ~ m1_subset_1(X35,u1_struct_0(k2_yellow_1(X34)))
        | v1_xboole_0(X34) )
      & ( ~ r1_tarski(X35,X36)
        | r3_orders_2(k2_yellow_1(X34),X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(k2_yellow_1(X34)))
        | ~ m1_subset_1(X35,u1_struct_0(k2_yellow_1(X34)))
        | v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_29,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),X3)
    | m1_subset_1(esk3_3(k2_yellow_1(X2),X1,X3),X2)
    | ~ r2_lattice3(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_30,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r3_orders_2(X19,X20,X21)
        | r1_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) )
      & ( ~ r1_orders_2(X19,X20,X21)
        | r3_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_36,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),k1_xboole_0)
    | m1_subset_1(esk3_3(k2_yellow_1(X2),X1,k1_xboole_0),X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23]),c_0_21])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k1_yellow_0(k2_yellow_1(esk4_0),k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23])])).

cnf(c_0_40,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_21]),c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_45,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_46,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_47,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_41]),c_0_23])])).

cnf(c_0_48,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk4_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_43])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_53,plain,(
    ! [X17] :
      ( ~ v2_struct_0(X17)
      | ~ l1_struct_0(X17)
      | v1_xboole_0(u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_54,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk4_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_57,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk3_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_38]),c_0_56])])).

cnf(c_0_61,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk4_0))
    | ~ r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_22]),c_0_23]),c_0_21]),c_0_38])]),c_0_39])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_21]),c_0_23])]),c_0_44])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_30]),c_0_23]),c_0_21]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:08:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.19/0.39  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.19/0.39  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.19/0.39  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.19/0.39  fof(t13_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.19/0.39  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.19/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.39  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.19/0.39  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.19/0.39  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.19/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.39  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.19/0.39  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.39  fof(c_0_15, plain, ![X23, X24, X25, X26, X27]:(((r2_lattice3(X23,X25,X24)|(X24!=k1_yellow_0(X23,X25)|~r1_yellow_0(X23,X25))|~m1_subset_1(X24,u1_struct_0(X23))|(~v5_orders_2(X23)|~l1_orders_2(X23)))&(~m1_subset_1(X26,u1_struct_0(X23))|(~r2_lattice3(X23,X25,X26)|r1_orders_2(X23,X24,X26))|(X24!=k1_yellow_0(X23,X25)|~r1_yellow_0(X23,X25))|~m1_subset_1(X24,u1_struct_0(X23))|(~v5_orders_2(X23)|~l1_orders_2(X23))))&(((X24=k1_yellow_0(X23,X27)|(m1_subset_1(esk3_3(X23,X24,X27),u1_struct_0(X23))|~r2_lattice3(X23,X27,X24))|~m1_subset_1(X24,u1_struct_0(X23))|(~v5_orders_2(X23)|~l1_orders_2(X23)))&(r1_yellow_0(X23,X27)|(m1_subset_1(esk3_3(X23,X24,X27),u1_struct_0(X23))|~r2_lattice3(X23,X27,X24))|~m1_subset_1(X24,u1_struct_0(X23))|(~v5_orders_2(X23)|~l1_orders_2(X23))))&(((X24=k1_yellow_0(X23,X27)|(r2_lattice3(X23,X27,esk3_3(X23,X24,X27))|~r2_lattice3(X23,X27,X24))|~m1_subset_1(X24,u1_struct_0(X23))|(~v5_orders_2(X23)|~l1_orders_2(X23)))&(r1_yellow_0(X23,X27)|(r2_lattice3(X23,X27,esk3_3(X23,X24,X27))|~r2_lattice3(X23,X27,X24))|~m1_subset_1(X24,u1_struct_0(X23))|(~v5_orders_2(X23)|~l1_orders_2(X23))))&((X24=k1_yellow_0(X23,X27)|(~r1_orders_2(X23,X24,esk3_3(X23,X24,X27))|~r2_lattice3(X23,X27,X24))|~m1_subset_1(X24,u1_struct_0(X23))|(~v5_orders_2(X23)|~l1_orders_2(X23)))&(r1_yellow_0(X23,X27)|(~r1_orders_2(X23,X24,esk3_3(X23,X24,X27))|~r2_lattice3(X23,X27,X24))|~m1_subset_1(X24,u1_struct_0(X23))|(~v5_orders_2(X23)|~l1_orders_2(X23))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.19/0.39  fof(c_0_16, plain, ![X33]:(u1_struct_0(k2_yellow_1(X33))=X33&u1_orders_2(k2_yellow_1(X33))=k1_yellow_1(X33)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.19/0.39  fof(c_0_17, plain, ![X32]:(((v1_orders_2(k2_yellow_1(X32))&v3_orders_2(k2_yellow_1(X32)))&v4_orders_2(k2_yellow_1(X32)))&v5_orders_2(k2_yellow_1(X32))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.19/0.39  fof(c_0_18, plain, ![X31]:(v1_orders_2(k2_yellow_1(X31))&l1_orders_2(k2_yellow_1(X31))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.19/0.39  fof(c_0_19, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0))), inference(assume_negation,[status(cth)],[t13_yellow_1])).
% 0.19/0.39  cnf(c_0_20, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk3_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_21, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_22, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_23, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  fof(c_0_24, plain, ![X29, X30]:((r2_lattice3(X29,k1_xboole_0,X30)|~m1_subset_1(X30,u1_struct_0(X29))|~l1_orders_2(X29))&(r1_lattice3(X29,k1_xboole_0,X30)|~m1_subset_1(X30,u1_struct_0(X29))|~l1_orders_2(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.19/0.39  fof(c_0_25, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.39  fof(c_0_26, negated_conjecture, (~v1_xboole_0(esk4_0)&(r2_hidden(k1_xboole_0,esk4_0)&k3_yellow_0(k2_yellow_1(esk4_0))!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.19/0.39  fof(c_0_27, plain, ![X22]:(~l1_orders_2(X22)|k3_yellow_0(X22)=k1_yellow_0(X22,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.19/0.39  fof(c_0_28, plain, ![X34, X35, X36]:((~r3_orders_2(k2_yellow_1(X34),X35,X36)|r1_tarski(X35,X36)|~m1_subset_1(X36,u1_struct_0(k2_yellow_1(X34)))|~m1_subset_1(X35,u1_struct_0(k2_yellow_1(X34)))|v1_xboole_0(X34))&(~r1_tarski(X35,X36)|r3_orders_2(k2_yellow_1(X34),X35,X36)|~m1_subset_1(X36,u1_struct_0(k2_yellow_1(X34)))|~m1_subset_1(X35,u1_struct_0(k2_yellow_1(X34)))|v1_xboole_0(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.19/0.39  cnf(c_0_29, plain, (X1=k1_yellow_0(k2_yellow_1(X2),X3)|m1_subset_1(esk3_3(k2_yellow_1(X2),X1,X3),X2)|~r2_lattice3(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 0.19/0.39  cnf(c_0_30, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(k1_xboole_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (k3_yellow_0(k2_yellow_1(esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_34, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  fof(c_0_35, plain, ![X19, X20, X21]:((~r3_orders_2(X19,X20,X21)|r1_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))&(~r1_orders_2(X19,X20,X21)|r3_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.19/0.39  cnf(c_0_36, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_37, plain, (X1=k1_yellow_0(k2_yellow_1(X2),k1_xboole_0)|m1_subset_1(esk3_3(k2_yellow_1(X2),X1,k1_xboole_0),X2)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_23]), c_0_21])])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (m1_subset_1(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (k1_yellow_0(k2_yellow_1(esk4_0),k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_23])])).
% 0.19/0.39  cnf(c_0_40, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  cnf(c_0_41, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_42, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_21]), c_0_21])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  fof(c_0_45, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.39  fof(c_0_46, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.39  cnf(c_0_47, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_41]), c_0_23])])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (r3_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|~m1_subset_1(X1,esk4_0)|~r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.19/0.39  cnf(c_0_49, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.39  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk4_0))|~m1_subset_1(X1,esk4_0)|~r1_tarski(X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_43])])).
% 0.19/0.39  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.39  fof(c_0_53, plain, ![X17]:(~v2_struct_0(X17)|~l1_struct_0(X17)|v1_xboole_0(u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.19/0.39  fof(c_0_54, plain, ![X18]:(~l1_orders_2(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (r1_orders_2(k2_yellow_1(esk4_0),X1,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk4_0))|~m1_subset_1(X1,esk4_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.39  cnf(c_0_56, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.39  cnf(c_0_57, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.39  cnf(c_0_58, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.39  cnf(c_0_59, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk3_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (r1_orders_2(k2_yellow_1(esk4_0),k1_xboole_0,esk3_3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_38]), c_0_56])])).
% 0.19/0.39  cnf(c_0_61, plain, (v1_xboole_0(u1_struct_0(X1))|~l1_orders_2(X1)|~v2_struct_0(X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, (v2_struct_0(k2_yellow_1(esk4_0))|~r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_22]), c_0_23]), c_0_21]), c_0_38])]), c_0_39])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (~r2_lattice3(k2_yellow_1(esk4_0),k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_21]), c_0_23])]), c_0_44])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_30]), c_0_23]), c_0_21]), c_0_38])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 65
% 0.19/0.39  # Proof object clause steps            : 35
% 0.19/0.39  # Proof object formula steps           : 30
% 0.19/0.39  # Proof object conjectures             : 16
% 0.19/0.39  # Proof object clause conjectures      : 13
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 19
% 0.19/0.39  # Proof object initial formulas used   : 15
% 0.19/0.39  # Proof object generating inferences   : 15
% 0.19/0.39  # Proof object simplifying inferences  : 33
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 15
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 35
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 34
% 0.19/0.39  # Processed clauses                    : 234
% 0.19/0.39  # ...of these trivial                  : 1
% 0.19/0.39  # ...subsumed                          : 21
% 0.19/0.39  # ...remaining for further processing  : 212
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 13
% 0.19/0.39  # Backward-rewritten                   : 17
% 0.19/0.39  # Generated clauses                    : 373
% 0.19/0.39  # ...of the previous two non-trivial   : 332
% 0.19/0.39  # Contextual simplify-reflections      : 23
% 0.19/0.39  # Paramodulations                      : 371
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 2
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 147
% 0.19/0.39  #    Positive orientable unit clauses  : 15
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 4
% 0.19/0.39  #    Non-unit-clauses                  : 128
% 0.19/0.39  # Current number of unprocessed clauses: 147
% 0.19/0.39  # ...number of literals in the above   : 778
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 64
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 5235
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1704
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 55
% 0.19/0.39  # Unit Clause-clause subsumption calls : 82
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 7
% 0.19/0.39  # BW rewrite match successes           : 3
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 14512
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.052 s
% 0.19/0.39  # System time              : 0.003 s
% 0.19/0.39  # Total time               : 0.055 s
% 0.19/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
