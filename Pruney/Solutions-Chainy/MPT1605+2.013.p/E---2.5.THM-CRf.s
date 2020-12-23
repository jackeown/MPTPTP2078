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
% DateTime   : Thu Dec  3 11:15:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 260 expanded)
%              Number of clauses        :   49 ( 108 expanded)
%              Number of leaves         :   15 (  69 expanded)
%              Depth                    :   19
%              Number of atoms          :  272 ( 729 expanded)
%              Number of equality atoms :   12 ( 116 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(d4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_yellow_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & r1_lattice3(X1,u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_yellow_0)).

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

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( r2_hidden(k1_xboole_0,X1)
         => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_1])).

fof(c_0_16,plain,(
    ! [X24,X25,X26,X27] :
      ( ( ~ r1_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ r2_hidden(X27,X25)
        | r1_orders_2(X24,X26,X27)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( m1_subset_1(esk3_3(X24,X25,X26),u1_struct_0(X24))
        | r1_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( r2_hidden(esk3_3(X24,X25,X26),X25)
        | r1_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( ~ r1_orders_2(X24,X26,esk3_3(X24,X25,X26))
        | r1_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_17,plain,(
    ! [X38] :
      ( u1_struct_0(k2_yellow_1(X38)) = X38
      & u1_orders_2(k2_yellow_1(X38)) = k1_yellow_1(X38) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_18,plain,(
    ! [X35] :
      ( v1_orders_2(k2_yellow_1(X35))
      & l1_orders_2(k2_yellow_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | m1_subset_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    & r2_hidden(k1_xboole_0,esk5_0)
    & k3_yellow_0(k2_yellow_1(esk5_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r3_orders_2(k2_yellow_1(X39),X40,X41)
        | r1_tarski(X40,X41)
        | ~ m1_subset_1(X41,u1_struct_0(k2_yellow_1(X39)))
        | ~ m1_subset_1(X40,u1_struct_0(k2_yellow_1(X39)))
        | v1_xboole_0(X39) )
      & ( ~ r1_tarski(X40,X41)
        | r3_orders_2(k2_yellow_1(X39),X40,X41)
        | ~ m1_subset_1(X41,u1_struct_0(k2_yellow_1(X39)))
        | ~ m1_subset_1(X40,u1_struct_0(k2_yellow_1(X39)))
        | v1_xboole_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_27,plain,
    ( r1_lattice3(k2_yellow_1(X1),X2,X3)
    | r2_hidden(esk3_3(k2_yellow_1(X1),X2,X3),X2)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)
    | r2_hidden(esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_22]),c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)
    | m1_subset_1(esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

fof(c_0_36,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_37,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r3_orders_2(X21,X22,X23)
        | r1_orders_2(X21,X22,X23)
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21)) )
      & ( ~ r1_orders_2(X21,X22,X23)
        | r3_orders_2(X21,X22,X23)
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_38,plain,(
    ! [X36] :
      ( v1_orders_2(k2_yellow_1(X36))
      & v3_orders_2(k2_yellow_1(X36))
      & v4_orders_2(k2_yellow_1(X36))
      & v5_orders_2(k2_yellow_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

cnf(c_0_39,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)
    | r3_orders_2(k2_yellow_1(X1),X2,esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0))
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)
    | r3_orders_2(k2_yellow_1(X1),k1_xboole_0,esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( r1_lattice3(k2_yellow_1(X1),X2,X3)
    | m1_subset_1(esk3_3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_23])])).

cnf(c_0_46,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_22]),c_0_23]),c_0_43])])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0)
    | r3_orders_2(k2_yellow_1(esk5_0),k1_xboole_0,esk3_3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)
    | m1_subset_1(esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_28])).

fof(c_0_49,plain,(
    ! [X29,X31] :
      ( ( m1_subset_1(esk4_1(X29),u1_struct_0(X29))
        | ~ v1_yellow_0(X29)
        | ~ l1_orders_2(X29) )
      & ( r1_lattice3(X29,u1_struct_0(X29),esk4_1(X29))
        | ~ v1_yellow_0(X29)
        | ~ l1_orders_2(X29) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ r1_lattice3(X29,u1_struct_0(X29),X31)
        | v1_yellow_0(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_yellow_0])])])])])).

fof(c_0_50,plain,(
    ! [X37] :
      ( ( ~ v2_struct_0(k2_yellow_1(X37))
        | v1_xboole_0(X37) )
      & ( v1_orders_2(k2_yellow_1(X37))
        | v1_xboole_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_51,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk3_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0)
    | r1_orders_2(k2_yellow_1(esk5_0),k1_xboole_0,esk3_3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0))
    | v2_struct_0(k2_yellow_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_28])]),c_0_48])).

fof(c_0_53,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v5_orders_2(X33)
      | ~ v1_yellow_0(X33)
      | ~ l1_orders_2(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | r1_orders_2(X33,k3_yellow_0(X33),X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

cnf(c_0_54,plain,
    ( v1_yellow_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,u1_struct_0(X2),X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0)
    | v2_struct_0(k2_yellow_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_23]),c_0_22]),c_0_28])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_60,plain,
    ( v1_yellow_0(k2_yellow_1(X1))
    | ~ r1_lattice3(k2_yellow_1(X1),X1,X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_23])])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattice3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_62,plain,
    ( r1_orders_2(k2_yellow_1(X1),k3_yellow_0(k2_yellow_1(X1)),X2)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ v1_yellow_0(k2_yellow_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_22]),c_0_59]),c_0_23])])).

cnf(c_0_63,negated_conjecture,
    ( v1_yellow_0(k2_yellow_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_28])])).

fof(c_0_64,plain,(
    ! [X32] :
      ( ~ l1_orders_2(X32)
      | m1_subset_1(k3_yellow_0(X32),u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_65,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk5_0),k3_yellow_0(k2_yellow_1(esk5_0)),X1)
    | v2_struct_0(k2_yellow_1(esk5_0))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_69,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_22]),c_0_23]),c_0_43])])).

cnf(c_0_70,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk5_0),k3_yellow_0(k2_yellow_1(esk5_0)),k1_xboole_0)
    | v2_struct_0(k2_yellow_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_28])).

cnf(c_0_71,plain,
    ( m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_22]),c_0_23])])).

fof(c_0_72,plain,(
    ! [X16] :
      ( ~ r1_tarski(X16,k1_xboole_0)
      | X16 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | v1_xboole_0(X3)
    | ~ r3_orders_2(k2_yellow_1(X3),X1,X2)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_22]),c_0_22])).

cnf(c_0_74,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk5_0),k3_yellow_0(k2_yellow_1(esk5_0)),k1_xboole_0)
    | v2_struct_0(k2_yellow_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_28]),c_0_71])])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk5_0))
    | r1_tarski(k3_yellow_0(k2_yellow_1(esk5_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_28]),c_0_71])]),c_0_57])).

cnf(c_0_77,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_78]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:57:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.029 s
% 0.20/0.49  # Presaturation interreduction done
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t13_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.20/0.49  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.20/0.49  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.49  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.49  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.49  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.20/0.49  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.49  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.49  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.49  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.20/0.49  fof(d4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>(v1_yellow_0(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&r1_lattice3(X1,u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_yellow_0)).
% 0.20/0.49  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.20/0.49  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.20/0.49  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.20/0.49  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.49  fof(c_0_15, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0))), inference(assume_negation,[status(cth)],[t13_yellow_1])).
% 0.20/0.49  fof(c_0_16, plain, ![X24, X25, X26, X27]:((~r1_lattice3(X24,X25,X26)|(~m1_subset_1(X27,u1_struct_0(X24))|(~r2_hidden(X27,X25)|r1_orders_2(X24,X26,X27)))|~m1_subset_1(X26,u1_struct_0(X24))|~l1_orders_2(X24))&((m1_subset_1(esk3_3(X24,X25,X26),u1_struct_0(X24))|r1_lattice3(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~l1_orders_2(X24))&((r2_hidden(esk3_3(X24,X25,X26),X25)|r1_lattice3(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~l1_orders_2(X24))&(~r1_orders_2(X24,X26,esk3_3(X24,X25,X26))|r1_lattice3(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~l1_orders_2(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.20/0.49  fof(c_0_17, plain, ![X38]:(u1_struct_0(k2_yellow_1(X38))=X38&u1_orders_2(k2_yellow_1(X38))=k1_yellow_1(X38)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.49  fof(c_0_18, plain, ![X35]:(v1_orders_2(k2_yellow_1(X35))&l1_orders_2(k2_yellow_1(X35))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.49  fof(c_0_19, plain, ![X19, X20]:(~r2_hidden(X19,X20)|m1_subset_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.49  fof(c_0_20, negated_conjecture, (~v1_xboole_0(esk5_0)&(r2_hidden(k1_xboole_0,esk5_0)&k3_yellow_0(k2_yellow_1(esk5_0))!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.49  cnf(c_0_21, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_22, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.49  cnf(c_0_23, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  cnf(c_0_24, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.49  cnf(c_0_25, negated_conjecture, (r2_hidden(k1_xboole_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.49  fof(c_0_26, plain, ![X39, X40, X41]:((~r3_orders_2(k2_yellow_1(X39),X40,X41)|r1_tarski(X40,X41)|~m1_subset_1(X41,u1_struct_0(k2_yellow_1(X39)))|~m1_subset_1(X40,u1_struct_0(k2_yellow_1(X39)))|v1_xboole_0(X39))&(~r1_tarski(X40,X41)|r3_orders_2(k2_yellow_1(X39),X40,X41)|~m1_subset_1(X41,u1_struct_0(k2_yellow_1(X39)))|~m1_subset_1(X40,u1_struct_0(k2_yellow_1(X39)))|v1_xboole_0(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.20/0.49  cnf(c_0_27, plain, (r1_lattice3(k2_yellow_1(X1),X2,X3)|r2_hidden(esk3_3(k2_yellow_1(X1),X2,X3),X2)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.20/0.49  cnf(c_0_28, negated_conjecture, (m1_subset_1(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.49  fof(c_0_29, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.49  cnf(c_0_30, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.49  cnf(c_0_31, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)|r2_hidden(esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.49  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.49  cnf(c_0_33, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_22]), c_0_22])).
% 0.20/0.49  cnf(c_0_34, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)|m1_subset_1(esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_31])).
% 0.20/0.49  cnf(c_0_35, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.20/0.49  fof(c_0_36, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.49  fof(c_0_37, plain, ![X21, X22, X23]:((~r3_orders_2(X21,X22,X23)|r1_orders_2(X21,X22,X23)|(v2_struct_0(X21)|~v3_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))))&(~r1_orders_2(X21,X22,X23)|r3_orders_2(X21,X22,X23)|(v2_struct_0(X21)|~v3_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.49  fof(c_0_38, plain, ![X36]:(((v1_orders_2(k2_yellow_1(X36))&v3_orders_2(k2_yellow_1(X36)))&v4_orders_2(k2_yellow_1(X36)))&v5_orders_2(k2_yellow_1(X36))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.20/0.49  cnf(c_0_39, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)|r3_orders_2(k2_yellow_1(X1),X2,esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0))|~m1_subset_1(X2,X1)|~r1_tarski(X2,esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.20/0.49  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.49  cnf(c_0_41, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_42, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.49  cnf(c_0_43, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  cnf(c_0_44, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)|r3_orders_2(k2_yellow_1(X1),k1_xboole_0,esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0))|~m1_subset_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.49  cnf(c_0_45, plain, (r1_lattice3(k2_yellow_1(X1),X2,X3)|m1_subset_1(esk3_3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_22]), c_0_23])])).
% 0.20/0.49  cnf(c_0_46, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_22]), c_0_23]), c_0_43])])).
% 0.20/0.49  cnf(c_0_47, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0)|r3_orders_2(k2_yellow_1(esk5_0),k1_xboole_0,esk3_3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_44, c_0_28])).
% 0.20/0.49  cnf(c_0_48, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),X1,k1_xboole_0)|m1_subset_1(esk3_3(k2_yellow_1(esk5_0),X1,k1_xboole_0),esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_28])).
% 0.20/0.49  fof(c_0_49, plain, ![X29, X31]:(((m1_subset_1(esk4_1(X29),u1_struct_0(X29))|~v1_yellow_0(X29)|~l1_orders_2(X29))&(r1_lattice3(X29,u1_struct_0(X29),esk4_1(X29))|~v1_yellow_0(X29)|~l1_orders_2(X29)))&(~m1_subset_1(X31,u1_struct_0(X29))|~r1_lattice3(X29,u1_struct_0(X29),X31)|v1_yellow_0(X29)|~l1_orders_2(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_yellow_0])])])])])).
% 0.20/0.49  fof(c_0_50, plain, ![X37]:((~v2_struct_0(k2_yellow_1(X37))|v1_xboole_0(X37))&(v1_orders_2(k2_yellow_1(X37))|v1_xboole_0(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.20/0.49  cnf(c_0_51, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk3_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_52, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0)|r1_orders_2(k2_yellow_1(esk5_0),k1_xboole_0,esk3_3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0))|v2_struct_0(k2_yellow_1(esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_28])]), c_0_48])).
% 0.20/0.49  fof(c_0_53, plain, ![X33, X34]:(v2_struct_0(X33)|~v5_orders_2(X33)|~v1_yellow_0(X33)|~l1_orders_2(X33)|(~m1_subset_1(X34,u1_struct_0(X33))|r1_orders_2(X33,k3_yellow_0(X33),X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.20/0.49  cnf(c_0_54, plain, (v1_yellow_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,u1_struct_0(X2),X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.49  cnf(c_0_55, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.49  cnf(c_0_56, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0)|v2_struct_0(k2_yellow_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_23]), c_0_22]), c_0_28])])).
% 0.20/0.49  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.49  cnf(c_0_58, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.49  cnf(c_0_59, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  cnf(c_0_60, plain, (v1_yellow_0(k2_yellow_1(X1))|~r1_lattice3(k2_yellow_1(X1),X1,X2)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_22]), c_0_23])])).
% 0.20/0.49  cnf(c_0_61, negated_conjecture, (r1_lattice3(k2_yellow_1(esk5_0),esk5_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.20/0.49  cnf(c_0_62, plain, (r1_orders_2(k2_yellow_1(X1),k3_yellow_0(k2_yellow_1(X1)),X2)|v2_struct_0(k2_yellow_1(X1))|~v1_yellow_0(k2_yellow_1(X1))|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_22]), c_0_59]), c_0_23])])).
% 0.20/0.49  cnf(c_0_63, negated_conjecture, (v1_yellow_0(k2_yellow_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_28])])).
% 0.20/0.49  fof(c_0_64, plain, ![X32]:(~l1_orders_2(X32)|m1_subset_1(k3_yellow_0(X32),u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.20/0.49  cnf(c_0_65, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.49  cnf(c_0_66, negated_conjecture, (r1_orders_2(k2_yellow_1(esk5_0),k3_yellow_0(k2_yellow_1(esk5_0)),X1)|v2_struct_0(k2_yellow_1(esk5_0))|~m1_subset_1(X1,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.49  cnf(c_0_67, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.49  cnf(c_0_68, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.49  cnf(c_0_69, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_22]), c_0_23]), c_0_43])])).
% 0.20/0.49  cnf(c_0_70, negated_conjecture, (r1_orders_2(k2_yellow_1(esk5_0),k3_yellow_0(k2_yellow_1(esk5_0)),k1_xboole_0)|v2_struct_0(k2_yellow_1(esk5_0))), inference(spm,[status(thm)],[c_0_66, c_0_28])).
% 0.20/0.49  cnf(c_0_71, plain, (m1_subset_1(k3_yellow_0(k2_yellow_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_22]), c_0_23])])).
% 0.20/0.49  fof(c_0_72, plain, ![X16]:(~r1_tarski(X16,k1_xboole_0)|X16=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.49  cnf(c_0_73, plain, (r1_tarski(X1,X2)|v1_xboole_0(X3)|~r3_orders_2(k2_yellow_1(X3),X1,X2)|~m1_subset_1(X2,X3)|~m1_subset_1(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_22]), c_0_22])).
% 0.20/0.49  cnf(c_0_74, negated_conjecture, (r3_orders_2(k2_yellow_1(esk5_0),k3_yellow_0(k2_yellow_1(esk5_0)),k1_xboole_0)|v2_struct_0(k2_yellow_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_28]), c_0_71])])).
% 0.20/0.49  cnf(c_0_75, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.49  cnf(c_0_76, negated_conjecture, (v2_struct_0(k2_yellow_1(esk5_0))|r1_tarski(k3_yellow_0(k2_yellow_1(esk5_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_28]), c_0_71])]), c_0_57])).
% 0.20/0.49  cnf(c_0_77, negated_conjecture, (k3_yellow_0(k2_yellow_1(esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.49  cnf(c_0_78, negated_conjecture, (v2_struct_0(k2_yellow_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.20/0.49  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_78]), c_0_57]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 80
% 0.20/0.49  # Proof object clause steps            : 49
% 0.20/0.49  # Proof object formula steps           : 31
% 0.20/0.49  # Proof object conjectures             : 24
% 0.20/0.49  # Proof object clause conjectures      : 21
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 22
% 0.20/0.49  # Proof object initial formulas used   : 15
% 0.20/0.49  # Proof object generating inferences   : 25
% 0.20/0.49  # Proof object simplifying inferences  : 41
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 17
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 38
% 0.20/0.49  # Removed in clause preprocessing      : 1
% 0.20/0.49  # Initial clauses in saturation        : 37
% 0.20/0.49  # Processed clauses                    : 1702
% 0.20/0.49  # ...of these trivial                  : 4
% 0.20/0.49  # ...subsumed                          : 1159
% 0.20/0.49  # ...remaining for further processing  : 539
% 0.20/0.49  # Other redundant clauses eliminated   : 0
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 39
% 0.20/0.49  # Backward-rewritten                   : 78
% 0.20/0.49  # Generated clauses                    : 2849
% 0.20/0.49  # ...of the previous two non-trivial   : 2539
% 0.20/0.49  # Contextual simplify-reflections      : 53
% 0.20/0.49  # Paramodulations                      : 2849
% 0.20/0.49  # Factorizations                       : 0
% 0.20/0.49  # Equation resolutions                 : 0
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 388
% 0.20/0.49  #    Positive orientable unit clauses  : 23
% 0.20/0.49  #    Positive unorientable unit clauses: 0
% 0.20/0.49  #    Negative unit clauses             : 2
% 0.20/0.49  #    Non-unit-clauses                  : 363
% 0.20/0.49  # Current number of unprocessed clauses: 895
% 0.20/0.49  # ...number of literals in the above   : 4106
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 152
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 36947
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 18264
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 1094
% 0.20/0.49  # Unit Clause-clause subsumption calls : 1800
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 47
% 0.20/0.49  # BW rewrite match successes           : 14
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 67780
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.141 s
% 0.20/0.49  # System time              : 0.004 s
% 0.20/0.49  # Total time               : 0.145 s
% 0.20/0.49  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
