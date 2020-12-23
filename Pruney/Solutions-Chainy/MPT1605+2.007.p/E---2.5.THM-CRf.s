%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 196 expanded)
%              Number of clauses        :   35 (  79 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 ( 666 expanded)
%              Number of equality atoms :   24 ( 118 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   50 (   2 average)
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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(c_0_15,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( r2_lattice3(X24,X26,X25)
        | X25 != k1_yellow_0(X24,X26)
        | ~ r1_yellow_0(X24,X26)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ r2_lattice3(X24,X26,X27)
        | r1_orders_2(X24,X25,X27)
        | X25 != k1_yellow_0(X24,X26)
        | ~ r1_yellow_0(X24,X26)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( X25 = k1_yellow_0(X24,X28)
        | m1_subset_1(esk2_3(X24,X25,X28),u1_struct_0(X24))
        | ~ r2_lattice3(X24,X28,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( r1_yellow_0(X24,X28)
        | m1_subset_1(esk2_3(X24,X25,X28),u1_struct_0(X24))
        | ~ r2_lattice3(X24,X28,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( X25 = k1_yellow_0(X24,X28)
        | r2_lattice3(X24,X28,esk2_3(X24,X25,X28))
        | ~ r2_lattice3(X24,X28,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( r1_yellow_0(X24,X28)
        | r2_lattice3(X24,X28,esk2_3(X24,X25,X28))
        | ~ r2_lattice3(X24,X28,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( X25 = k1_yellow_0(X24,X28)
        | ~ r1_orders_2(X24,X25,esk2_3(X24,X25,X28))
        | ~ r2_lattice3(X24,X28,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( r1_yellow_0(X24,X28)
        | ~ r1_orders_2(X24,X25,esk2_3(X24,X25,X28))
        | ~ r2_lattice3(X24,X28,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_16,plain,(
    ! [X35] :
      ( u1_struct_0(k2_yellow_1(X35)) = X35
      & u1_orders_2(k2_yellow_1(X35)) = k1_yellow_1(X35) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_17,plain,(
    ! [X33] :
      ( v1_orders_2(k2_yellow_1(X33))
      & v3_orders_2(k2_yellow_1(X33))
      & v4_orders_2(k2_yellow_1(X33))
      & v5_orders_2(k2_yellow_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_18,plain,(
    ! [X32] :
      ( v1_orders_2(k2_yellow_1(X32))
      & l1_orders_2(k2_yellow_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( r2_hidden(k1_xboole_0,X1)
         => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_1])).

cnf(c_0_20,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
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
    ! [X30,X31] :
      ( ( r2_lattice3(X30,k1_xboole_0,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( r1_lattice3(X30,k1_xboole_0,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_25,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | m1_subset_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & r2_hidden(k1_xboole_0,esk3_0)
    & k3_yellow_0(k2_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_27,plain,(
    ! [X23] :
      ( ~ l1_orders_2(X23)
      | k3_yellow_0(X23) = k1_yellow_0(X23,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_28,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r3_orders_2(k2_yellow_1(X36),X37,X38)
        | r1_tarski(X37,X38)
        | ~ m1_subset_1(X38,u1_struct_0(k2_yellow_1(X36)))
        | ~ m1_subset_1(X37,u1_struct_0(k2_yellow_1(X36)))
        | v1_xboole_0(X36) )
      & ( ~ r1_tarski(X37,X38)
        | r3_orders_2(k2_yellow_1(X36),X37,X38)
        | ~ m1_subset_1(X38,u1_struct_0(k2_yellow_1(X36)))
        | ~ m1_subset_1(X37,u1_struct_0(k2_yellow_1(X36)))
        | v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_29,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),X3)
    | m1_subset_1(esk2_3(k2_yellow_1(X2),X1,X3),X2)
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
    ( r2_hidden(k1_xboole_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_36,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_37,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r3_orders_2(X20,X21,X22)
        | r1_orders_2(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) )
      & ( ~ r1_orders_2(X20,X21,X22)
        | r3_orders_2(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_38,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( X1 = k1_yellow_0(k2_yellow_1(X2),k1_xboole_0)
    | m1_subset_1(esk2_3(k2_yellow_1(X2),X1,k1_xboole_0),X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23]),c_0_21])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k1_yellow_0(k2_yellow_1(esk3_0),k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23])])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_21]),c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_50,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_21]),c_0_23]),c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk3_0),X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))
    | ~ m1_subset_1(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk3_0),X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk3_0))
    | ~ m1_subset_1(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_48])])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_58,plain,(
    ! [X34] :
      ( ( ~ v2_struct_0(k2_yellow_1(X34))
        | v1_xboole_0(X34) )
      & ( v1_orders_2(k2_yellow_1(X34))
        | v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_59,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_40])])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk3_0))
    | ~ r2_lattice3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_22]),c_0_23]),c_0_21]),c_0_40])]),c_0_41])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_lattice3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_30]),c_0_23]),c_0_21]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:31:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.20/0.39  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.39  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.20/0.39  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.39  fof(t13_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.20/0.39  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.20/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.39  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.20/0.39  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.20/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.39  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.39  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.20/0.39  fof(c_0_15, plain, ![X24, X25, X26, X27, X28]:(((r2_lattice3(X24,X26,X25)|(X25!=k1_yellow_0(X24,X26)|~r1_yellow_0(X24,X26))|~m1_subset_1(X25,u1_struct_0(X24))|(~v5_orders_2(X24)|~l1_orders_2(X24)))&(~m1_subset_1(X27,u1_struct_0(X24))|(~r2_lattice3(X24,X26,X27)|r1_orders_2(X24,X25,X27))|(X25!=k1_yellow_0(X24,X26)|~r1_yellow_0(X24,X26))|~m1_subset_1(X25,u1_struct_0(X24))|(~v5_orders_2(X24)|~l1_orders_2(X24))))&(((X25=k1_yellow_0(X24,X28)|(m1_subset_1(esk2_3(X24,X25,X28),u1_struct_0(X24))|~r2_lattice3(X24,X28,X25))|~m1_subset_1(X25,u1_struct_0(X24))|(~v5_orders_2(X24)|~l1_orders_2(X24)))&(r1_yellow_0(X24,X28)|(m1_subset_1(esk2_3(X24,X25,X28),u1_struct_0(X24))|~r2_lattice3(X24,X28,X25))|~m1_subset_1(X25,u1_struct_0(X24))|(~v5_orders_2(X24)|~l1_orders_2(X24))))&(((X25=k1_yellow_0(X24,X28)|(r2_lattice3(X24,X28,esk2_3(X24,X25,X28))|~r2_lattice3(X24,X28,X25))|~m1_subset_1(X25,u1_struct_0(X24))|(~v5_orders_2(X24)|~l1_orders_2(X24)))&(r1_yellow_0(X24,X28)|(r2_lattice3(X24,X28,esk2_3(X24,X25,X28))|~r2_lattice3(X24,X28,X25))|~m1_subset_1(X25,u1_struct_0(X24))|(~v5_orders_2(X24)|~l1_orders_2(X24))))&((X25=k1_yellow_0(X24,X28)|(~r1_orders_2(X24,X25,esk2_3(X24,X25,X28))|~r2_lattice3(X24,X28,X25))|~m1_subset_1(X25,u1_struct_0(X24))|(~v5_orders_2(X24)|~l1_orders_2(X24)))&(r1_yellow_0(X24,X28)|(~r1_orders_2(X24,X25,esk2_3(X24,X25,X28))|~r2_lattice3(X24,X28,X25))|~m1_subset_1(X25,u1_struct_0(X24))|(~v5_orders_2(X24)|~l1_orders_2(X24))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.20/0.39  fof(c_0_16, plain, ![X35]:(u1_struct_0(k2_yellow_1(X35))=X35&u1_orders_2(k2_yellow_1(X35))=k1_yellow_1(X35)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.39  fof(c_0_17, plain, ![X33]:(((v1_orders_2(k2_yellow_1(X33))&v3_orders_2(k2_yellow_1(X33)))&v4_orders_2(k2_yellow_1(X33)))&v5_orders_2(k2_yellow_1(X33))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.20/0.39  fof(c_0_18, plain, ![X32]:(v1_orders_2(k2_yellow_1(X32))&l1_orders_2(k2_yellow_1(X32))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.39  fof(c_0_19, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0))), inference(assume_negation,[status(cth)],[t13_yellow_1])).
% 0.20/0.39  cnf(c_0_20, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_21, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_22, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_23, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  fof(c_0_24, plain, ![X30, X31]:((r2_lattice3(X30,k1_xboole_0,X31)|~m1_subset_1(X31,u1_struct_0(X30))|~l1_orders_2(X30))&(r1_lattice3(X30,k1_xboole_0,X31)|~m1_subset_1(X31,u1_struct_0(X30))|~l1_orders_2(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.20/0.39  fof(c_0_25, plain, ![X12, X13]:(~r2_hidden(X12,X13)|m1_subset_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.39  fof(c_0_26, negated_conjecture, (~v1_xboole_0(esk3_0)&(r2_hidden(k1_xboole_0,esk3_0)&k3_yellow_0(k2_yellow_1(esk3_0))!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.20/0.39  fof(c_0_27, plain, ![X23]:(~l1_orders_2(X23)|k3_yellow_0(X23)=k1_yellow_0(X23,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.20/0.39  fof(c_0_28, plain, ![X36, X37, X38]:((~r3_orders_2(k2_yellow_1(X36),X37,X38)|r1_tarski(X37,X38)|~m1_subset_1(X38,u1_struct_0(k2_yellow_1(X36)))|~m1_subset_1(X37,u1_struct_0(k2_yellow_1(X36)))|v1_xboole_0(X36))&(~r1_tarski(X37,X38)|r3_orders_2(k2_yellow_1(X36),X37,X38)|~m1_subset_1(X38,u1_struct_0(k2_yellow_1(X36)))|~m1_subset_1(X37,u1_struct_0(k2_yellow_1(X36)))|v1_xboole_0(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.20/0.39  cnf(c_0_29, plain, (X1=k1_yellow_0(k2_yellow_1(X2),X3)|m1_subset_1(esk2_3(k2_yellow_1(X2),X1,X3),X2)|~r2_lattice3(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 0.20/0.39  cnf(c_0_30, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(k1_xboole_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (k3_yellow_0(k2_yellow_1(esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_34, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  fof(c_0_35, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.39  fof(c_0_36, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.39  fof(c_0_37, plain, ![X20, X21, X22]:((~r3_orders_2(X20,X21,X22)|r1_orders_2(X20,X21,X22)|(v2_struct_0(X20)|~v3_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))))&(~r1_orders_2(X20,X21,X22)|r3_orders_2(X20,X21,X22)|(v2_struct_0(X20)|~v3_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.39  cnf(c_0_38, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_39, plain, (X1=k1_yellow_0(k2_yellow_1(X2),k1_xboole_0)|m1_subset_1(esk2_3(k2_yellow_1(X2),X1,k1_xboole_0),X2)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_23]), c_0_21])])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (m1_subset_1(k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (k1_yellow_0(k2_yellow_1(esk3_0),k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_23])])).
% 0.20/0.39  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_43, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  fof(c_0_44, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  cnf(c_0_45, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_46, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_47, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_21]), c_0_21])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_50, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.39  cnf(c_0_51, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_52, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_21]), c_0_23]), c_0_46])])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (r3_orders_2(k2_yellow_1(esk3_0),X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))|~m1_subset_1(X1,esk3_0)|~r1_tarski(X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.20/0.39  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.39  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (r1_orders_2(k2_yellow_1(esk3_0),X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk3_0))|~m1_subset_1(X1,esk3_0)|~r1_tarski(X1,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_48])])).
% 0.20/0.39  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.39  fof(c_0_58, plain, ![X34]:((~v2_struct_0(k2_yellow_1(X34))|v1_xboole_0(X34))&(v1_orders_2(k2_yellow_1(X34))|v1_xboole_0(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.20/0.39  cnf(c_0_59, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (r1_orders_2(k2_yellow_1(esk3_0),k1_xboole_0,esk2_3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_40])])).
% 0.20/0.39  cnf(c_0_61, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (v2_struct_0(k2_yellow_1(esk3_0))|~r2_lattice3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_22]), c_0_23]), c_0_21]), c_0_40])]), c_0_41])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (~r2_lattice3(k2_yellow_1(esk3_0),k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_49])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_30]), c_0_23]), c_0_21]), c_0_40])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 65
% 0.20/0.39  # Proof object clause steps            : 35
% 0.20/0.39  # Proof object formula steps           : 30
% 0.20/0.39  # Proof object conjectures             : 15
% 0.20/0.39  # Proof object clause conjectures      : 12
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 19
% 0.20/0.39  # Proof object initial formulas used   : 15
% 0.20/0.39  # Proof object generating inferences   : 15
% 0.20/0.39  # Proof object simplifying inferences  : 30
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 16
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 36
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 35
% 0.20/0.39  # Processed clauses                    : 166
% 0.20/0.39  # ...of these trivial                  : 2
% 0.20/0.39  # ...subsumed                          : 8
% 0.20/0.39  # ...remaining for further processing  : 156
% 0.20/0.39  # Other redundant clauses eliminated   : 2
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 5
% 0.20/0.39  # Backward-rewritten                   : 8
% 0.20/0.39  # Generated clauses                    : 222
% 0.20/0.39  # ...of the previous two non-trivial   : 202
% 0.20/0.39  # Contextual simplify-reflections      : 8
% 0.20/0.39  # Paramodulations                      : 220
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 2
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 108
% 0.20/0.39  #    Positive orientable unit clauses  : 15
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 89
% 0.20/0.39  # Current number of unprocessed clauses: 94
% 0.20/0.39  # ...number of literals in the above   : 465
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 47
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1728
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 493
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 20
% 0.20/0.39  # Unit Clause-clause subsumption calls : 48
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 5
% 0.20/0.39  # BW rewrite match successes           : 3
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 9469
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.043 s
% 0.20/0.39  # System time              : 0.003 s
% 0.20/0.39  # Total time               : 0.046 s
% 0.20/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
