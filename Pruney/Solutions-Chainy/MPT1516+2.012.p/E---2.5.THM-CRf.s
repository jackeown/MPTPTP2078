%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:07 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  136 (11340 expanded)
%              Number of clauses        :  105 (4021 expanded)
%              Number of leaves         :   15 (2733 expanded)
%              Depth                    :   26
%              Number of atoms          :  637 (72675 expanded)
%              Number of equality atoms :  110 (7272 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1)
        & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t45_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( X2 = k15_lattice3(X1,a_2_3_lattice3(X1,X2))
            & X2 = k16_lattice3(X1,a_2_4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(fraenkel_a_2_4_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_4_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r3_lattices(X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).

fof(t46_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
            & r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(d16_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(t34_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k16_lattice3(X1,X3)
            <=> ( r3_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_lattice3(X1,X4,X3)
                     => r3_lattices(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(d13_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k2_lattices(X1,X2,X3) = X2
                  & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(d6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v6_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(t21_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1)
          & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t50_lattice3])).

fof(c_0_16,plain,(
    ! [X12] :
      ( ( l1_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( l2_lattices(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v10_lattices(esk9_0)
    & v4_lattice3(esk9_0)
    & l3_lattices(esk9_0)
    & ( v2_struct_0(esk9_0)
      | ~ v10_lattices(esk9_0)
      | ~ v13_lattices(esk9_0)
      | ~ l3_lattices(esk9_0)
      | k5_lattices(esk9_0) != k15_lattice3(esk9_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X45,X46] :
      ( ( X46 = k15_lattice3(X45,a_2_3_lattice3(X45,X46))
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | v2_struct_0(X45)
        | ~ v10_lattices(X45)
        | ~ v4_lattice3(X45)
        | ~ l3_lattices(X45) )
      & ( X46 = k16_lattice3(X45,a_2_4_lattice3(X45,X46))
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | v2_struct_0(X45)
        | ~ v10_lattices(X45)
        | ~ v4_lattice3(X45)
        | ~ l3_lattices(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

fof(c_0_19,plain,(
    ! [X11] :
      ( v2_struct_0(X11)
      | ~ l1_lattices(X11)
      | m1_subset_1(k5_lattices(X11),u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_20,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l3_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v4_lattice3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_28,plain,(
    ! [X34,X35,X36,X38] :
      ( ( m1_subset_1(esk7_3(X34,X35,X36),u1_struct_0(X35))
        | ~ r2_hidden(X34,a_2_4_lattice3(X35,X36))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35)) )
      & ( X34 = esk7_3(X34,X35,X36)
        | ~ r2_hidden(X34,a_2_4_lattice3(X35,X36))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35)) )
      & ( r3_lattices(X35,X36,esk7_3(X34,X35,X36))
        | ~ r2_hidden(X34,a_2_4_lattice3(X35,X36))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35)) )
      & ( ~ m1_subset_1(X38,u1_struct_0(X35))
        | X34 != X38
        | ~ r3_lattices(X35,X36,X38)
        | r2_hidden(X34,a_2_4_lattice3(X35,X36))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).

fof(c_0_29,plain,(
    ! [X47,X48,X49] :
      ( ( r3_lattices(X47,k15_lattice3(X47,X48),k15_lattice3(X47,X49))
        | ~ r1_tarski(X48,X49)
        | v2_struct_0(X47)
        | ~ v10_lattices(X47)
        | ~ v4_lattice3(X47)
        | ~ l3_lattices(X47) )
      & ( r3_lattices(X47,k16_lattice3(X47,X49),k16_lattice3(X47,X48))
        | ~ r1_tarski(X48,X49)
        | v2_struct_0(X47)
        | ~ v10_lattices(X47)
        | ~ v4_lattice3(X47)
        | ~ l3_lattices(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).

cnf(c_0_30,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,X1)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk9_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,a_2_4_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,X4,X1)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_tarski(X2,X3)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0))) = k5_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_35,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_36,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ l3_lattices(X32)
      | m1_subset_1(k15_lattice3(X32,X33),u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_37,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r3_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r2_hidden(X24,X23)
        | r1_lattices(X21,X22,X24)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( m1_subset_1(esk4_3(X21,X22,X25),u1_struct_0(X21))
        | r3_lattice3(X21,X22,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( r2_hidden(esk4_3(X21,X22,X25),X25)
        | r3_lattice3(X21,X22,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( ~ r1_lattices(X21,X22,esk4_3(X21,X22,X25))
        | r3_lattice3(X21,X22,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X3,X1)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))
    | ~ r1_tarski(X1,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23]),c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,a_2_4_lattice3(esk9_0,X2))
    | ~ r3_lattices(esk9_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_23]),c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk9_0,X1),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_25])).

fof(c_0_46,plain,(
    ! [X39,X40,X41,X42,X43] :
      ( ( r3_lattice3(X39,X40,X41)
        | X40 != k16_lattice3(X39,X41)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) )
      & ( ~ m1_subset_1(X42,u1_struct_0(X39))
        | ~ r3_lattice3(X39,X42,X41)
        | r3_lattices(X39,X42,X40)
        | X40 != k16_lattice3(X39,X41)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) )
      & ( m1_subset_1(esk8_3(X39,X40,X43),u1_struct_0(X39))
        | ~ r3_lattice3(X39,X40,X43)
        | X40 = k16_lattice3(X39,X43)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) )
      & ( r3_lattice3(X39,esk8_3(X39,X40,X43),X43)
        | ~ r3_lattice3(X39,X40,X43)
        | X40 = k16_lattice3(X39,X43)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) )
      & ( ~ r3_lattices(X39,esk8_3(X39,X40,X43),X40)
        | ~ r3_lattice3(X39,X40,X43)
        | X40 = k16_lattice3(X39,X43)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_47,plain,
    ( X1 = k16_lattice3(X2,a_2_4_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_48,plain,(
    ! [X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v4_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v5_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v6_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v7_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v8_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v9_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_49,plain,(
    ! [X16,X18,X19] :
      ( ( m1_subset_1(esk2_1(X16),u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( k2_lattices(X16,esk2_1(X16),X18) = esk2_1(X16)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( k2_lattices(X16,X18,esk2_1(X16)) = esk2_1(X16)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( m1_subset_1(esk3_2(X16,X19),u1_struct_0(X16))
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( k2_lattices(X16,X19,esk3_2(X16,X19)) != X19
        | k2_lattices(X16,esk3_2(X16,X19),X19) != X19
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattices(esk9_0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r3_lattice3(esk9_0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k5_lattices(esk9_0),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_31])])).

cnf(c_0_52,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k16_lattice3(esk9_0,a_2_4_lattice3(esk9_0,X1)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_23]),c_0_24]),c_0_21])]),c_0_25])).

fof(c_0_54,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v6_lattices(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | k2_lattices(X27,X28,X29) = k2_lattices(X27,X29,X28)
        | v2_struct_0(X27)
        | ~ l1_lattices(X27) )
      & ( m1_subset_1(esk5_1(X27),u1_struct_0(X27))
        | v6_lattices(X27)
        | v2_struct_0(X27)
        | ~ l1_lattices(X27) )
      & ( m1_subset_1(esk6_1(X27),u1_struct_0(X27))
        | v6_lattices(X27)
        | v2_struct_0(X27)
        | ~ l1_lattices(X27) )
      & ( k2_lattices(X27,esk5_1(X27),esk6_1(X27)) != k2_lattices(X27,esk6_1(X27),esk5_1(X27))
        | v6_lattices(X27)
        | v2_struct_0(X27)
        | ~ l1_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_55,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_56,plain,(
    ! [X7,X8,X9] :
      ( ( k2_lattices(X7,X8,X9) = X8
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | X8 != k5_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v13_lattices(X7)
        | v2_struct_0(X7)
        | ~ l1_lattices(X7) )
      & ( k2_lattices(X7,X9,X8) = X8
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | X8 != k5_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v13_lattices(X7)
        | v2_struct_0(X7)
        | ~ l1_lattices(X7) )
      & ( m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))
        | X8 = k5_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v13_lattices(X7)
        | v2_struct_0(X7)
        | ~ l1_lattices(X7) )
      & ( k2_lattices(X7,X8,esk1_2(X7,X8)) != X8
        | k2_lattices(X7,esk1_2(X7,X8),X8) != X8
        | X8 = k5_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v13_lattices(X7)
        | v2_struct_0(X7)
        | ~ l1_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r1_lattices(X13,X14,X15)
        | k2_lattices(X13,X14,X15) = X14
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v8_lattices(X13)
        | ~ v9_lattices(X13)
        | ~ l3_lattices(X13) )
      & ( k2_lattices(X13,X14,X15) != X14
        | r1_lattices(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v8_lattices(X13)
        | ~ v9_lattices(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_59,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattices(esk9_0,X1,k5_lattices(esk9_0))
    | ~ r3_lattice3(esk9_0,X1,a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_31])])).

cnf(c_0_62,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k16_lattice3(esk9_0,a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,X1))) = k15_lattice3(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

cnf(c_0_64,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_66,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | X2 != k5_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk3_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v13_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_27]),c_0_25])).

cnf(c_0_68,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( v9_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_70,negated_conjecture,
    ( v8_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))
    | ~ r3_lattice3(esk9_0,k15_lattice3(esk9_0,X1),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_45])).

cnf(c_0_72,negated_conjecture,
    ( r3_lattice3(esk9_0,k15_lattice3(esk9_0,X1),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_23]),c_0_45]),c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( k2_lattices(esk9_0,X1,X2) = k2_lattices(esk9_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_65])]),c_0_25])).

cnf(c_0_74,plain,
    ( k2_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_26])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))
    | v13_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_45])).

cnf(c_0_76,negated_conjecture,
    ( r3_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_77,negated_conjecture,
    ( k2_lattices(esk9_0,X1,X2) = X1
    | ~ r1_lattices(esk9_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_21])]),c_0_25])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k2_lattices(esk9_0,X1,k5_lattices(esk9_0)) = k2_lattices(esk9_0,k5_lattices(esk9_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_31])).

cnf(c_0_80,negated_conjecture,
    ( k2_lattices(esk9_0,k5_lattices(esk9_0),X1) = k5_lattices(esk9_0)
    | m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_27])]),c_0_25])).

cnf(c_0_81,negated_conjecture,
    ( r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_40])).

cnf(c_0_82,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_31]),c_0_45])])).

cnf(c_0_83,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0)) = k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_45])).

cnf(c_0_84,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_85,negated_conjecture,
    ( k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X1)) = k5_lattices(esk9_0)
    | m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_45])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk9_0,X1),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_81]),c_0_45]),c_0_45])])).

cnf(c_0_87,negated_conjecture,
    ( k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r1_lattices(esk9_0,X1,X2)
    | k2_lattices(esk9_0,X1,X2) != X1
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_69]),c_0_70]),c_0_21])]),c_0_25])).

cnf(c_0_89,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X2)) = k5_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( v2_struct_0(esk9_0)
    | ~ v10_lattices(esk9_0)
    | ~ v13_lattices(esk9_0)
    | ~ l3_lattices(esk9_0)
    | k5_lattices(esk9_0) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_91,negated_conjecture,
    ( r1_lattices(esk9_0,X1,k15_lattice3(esk9_0,X2))
    | ~ r3_lattice3(esk9_0,X1,a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_86]),c_0_45])])).

cnf(c_0_92,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_93,negated_conjecture,
    ( k15_lattice3(esk9_0,k1_xboole_0) = k5_lattices(esk9_0)
    | ~ r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_87]),c_0_45]),c_0_31])])).

cnf(c_0_94,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_45]),c_0_31])])).

cnf(c_0_95,negated_conjecture,
    ( k15_lattice3(esk9_0,k1_xboole_0) != k5_lattices(esk9_0)
    | ~ v13_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_21]),c_0_24])]),c_0_25])).

cnf(c_0_96,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,X2))
    | ~ r3_lattice3(esk9_0,k15_lattice3(esk9_0,X1),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_45])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))
    | m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_75]),c_0_27])]),c_0_25])).

cnf(c_0_98,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | k15_lattice3(esk9_0,k1_xboole_0) = k5_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))
    | k15_lattice3(esk9_0,k1_xboole_0) != k5_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_75])).

cnf(c_0_100,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_101,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_72])).

cnf(c_0_102,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_98]),c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( v13_lattices(esk9_0)
    | k2_lattices(esk9_0,X1,esk3_2(esk9_0,X1)) != X1
    | k2_lattices(esk9_0,esk3_2(esk9_0,X1),X1) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_27]),c_0_25])).

cnf(c_0_105,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_101]),c_0_45]),c_0_45])])).

cnf(c_0_106,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( v13_lattices(esk9_0)
    | k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk3_2(esk9_0,k15_lattice3(esk9_0,X1))) != k15_lattice3(esk9_0,X1)
    | k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,X1)) != k15_lattice3(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_45])).

cnf(c_0_109,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1))) = k15_lattice3(esk9_0,k1_xboole_0)
    | k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_105]),c_0_45]),c_0_45])])).

cnf(c_0_111,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1))) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0)
    | v13_lattices(esk9_0)
    | k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0)) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0)
    | k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_106])).

cnf(c_0_114,negated_conjecture,
    ( v13_lattices(esk9_0)
    | k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0)) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_107])).

cnf(c_0_116,negated_conjecture,
    ( k2_lattices(esk9_0,X1,k15_lattice3(esk9_0,X2)) = k2_lattices(esk9_0,k15_lattice3(esk9_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_45])).

cnf(c_0_117,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0)
    | v13_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_118,plain,
    ( k2_lattices(X1,X2,esk2_1(X1)) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_119,negated_conjecture,
    ( v13_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115])])).

cnf(c_0_120,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,X2)) = k2_lattices(esk9_0,k15_lattice3(esk9_0,X2),k15_lattice3(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_45])).

cnf(c_0_121,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_117]),c_0_27])]),c_0_25]),c_0_30])).

cnf(c_0_122,negated_conjecture,
    ( k2_lattices(esk9_0,X1,esk2_1(esk9_0)) = esk2_1(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_27])]),c_0_25])).

cnf(c_0_123,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk2_1(esk9_0)) = k2_lattices(esk9_0,esk2_1(esk9_0),k15_lattice3(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_124,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_125,negated_conjecture,
    ( k2_lattices(esk9_0,esk2_1(esk9_0),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_121])).

cnf(c_0_126,negated_conjecture,
    ( k2_lattices(esk9_0,esk2_1(esk9_0),k15_lattice3(esk9_0,X1)) = esk2_1(esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_45]),c_0_123])).

cnf(c_0_127,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_124]),c_0_26])).

cnf(c_0_128,negated_conjecture,
    ( k15_lattice3(esk9_0,k1_xboole_0) != k5_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_119])])).

cnf(c_0_129,negated_conjecture,
    ( k15_lattice3(esk9_0,k1_xboole_0) = esk2_1(esk9_0) ),
    inference(rw,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_130,negated_conjecture,
    ( k2_lattices(esk9_0,X1,k5_lattices(esk9_0)) = k5_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_119]),c_0_27])]),c_0_25])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_121])).

cnf(c_0_132,negated_conjecture,
    ( k2_lattices(esk9_0,esk2_1(esk9_0),k5_lattices(esk9_0)) = k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_121])).

cnf(c_0_133,negated_conjecture,
    ( k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_31])).

cnf(c_0_134,negated_conjecture,
    ( esk2_1(esk9_0) != k5_lattices(esk9_0) ),
    inference(rw,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_135,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_132]),c_0_133]),c_0_134]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:37:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.18/0.52  # and selection function HSelectMinInfpos.
% 0.18/0.52  #
% 0.18/0.52  # Preprocessing time       : 0.030 s
% 0.18/0.52  # Presaturation interreduction done
% 0.18/0.52  
% 0.18/0.52  # Proof found!
% 0.18/0.52  # SZS status Theorem
% 0.18/0.52  # SZS output start CNFRefutation
% 0.18/0.52  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 0.18/0.52  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.18/0.52  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_lattice3)).
% 0.18/0.52  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.18/0.52  fof(fraenkel_a_2_4_lattice3, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))&m1_subset_1(X3,u1_struct_0(X2)))=>(r2_hidden(X1,a_2_4_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattices(X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_4_lattice3)).
% 0.18/0.52  fof(t46_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 0.18/0.52  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.52  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.18/0.52  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.18/0.52  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.18/0.52  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.18/0.52  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 0.18/0.52  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.18/0.52  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.18/0.52  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.18/0.52  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.18/0.52  fof(c_0_16, plain, ![X12]:((l1_lattices(X12)|~l3_lattices(X12))&(l2_lattices(X12)|~l3_lattices(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.18/0.52  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk9_0)&v10_lattices(esk9_0))&v4_lattice3(esk9_0))&l3_lattices(esk9_0))&(v2_struct_0(esk9_0)|~v10_lattices(esk9_0)|~v13_lattices(esk9_0)|~l3_lattices(esk9_0)|k5_lattices(esk9_0)!=k15_lattice3(esk9_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.18/0.52  fof(c_0_18, plain, ![X45, X46]:((X46=k15_lattice3(X45,a_2_3_lattice3(X45,X46))|~m1_subset_1(X46,u1_struct_0(X45))|(v2_struct_0(X45)|~v10_lattices(X45)|~v4_lattice3(X45)|~l3_lattices(X45)))&(X46=k16_lattice3(X45,a_2_4_lattice3(X45,X46))|~m1_subset_1(X46,u1_struct_0(X45))|(v2_struct_0(X45)|~v10_lattices(X45)|~v4_lattice3(X45)|~l3_lattices(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.18/0.52  fof(c_0_19, plain, ![X11]:(v2_struct_0(X11)|~l1_lattices(X11)|m1_subset_1(k5_lattices(X11),u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.18/0.52  cnf(c_0_20, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.52  cnf(c_0_21, negated_conjecture, (l3_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.52  cnf(c_0_22, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.52  cnf(c_0_23, negated_conjecture, (v4_lattice3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.52  cnf(c_0_24, negated_conjecture, (v10_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.52  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.52  cnf(c_0_26, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.52  cnf(c_0_27, negated_conjecture, (l1_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.52  fof(c_0_28, plain, ![X34, X35, X36, X38]:((((m1_subset_1(esk7_3(X34,X35,X36),u1_struct_0(X35))|~r2_hidden(X34,a_2_4_lattice3(X35,X36))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)|~m1_subset_1(X36,u1_struct_0(X35))))&(X34=esk7_3(X34,X35,X36)|~r2_hidden(X34,a_2_4_lattice3(X35,X36))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)|~m1_subset_1(X36,u1_struct_0(X35)))))&(r3_lattices(X35,X36,esk7_3(X34,X35,X36))|~r2_hidden(X34,a_2_4_lattice3(X35,X36))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)|~m1_subset_1(X36,u1_struct_0(X35)))))&(~m1_subset_1(X38,u1_struct_0(X35))|X34!=X38|~r3_lattices(X35,X36,X38)|r2_hidden(X34,a_2_4_lattice3(X35,X36))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)|~m1_subset_1(X36,u1_struct_0(X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).
% 0.18/0.52  fof(c_0_29, plain, ![X47, X48, X49]:((r3_lattices(X47,k15_lattice3(X47,X48),k15_lattice3(X47,X49))|~r1_tarski(X48,X49)|(v2_struct_0(X47)|~v10_lattices(X47)|~v4_lattice3(X47)|~l3_lattices(X47)))&(r3_lattices(X47,k16_lattice3(X47,X49),k16_lattice3(X47,X48))|~r1_tarski(X48,X49)|(v2_struct_0(X47)|~v10_lattices(X47)|~v4_lattice3(X47)|~l3_lattices(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).
% 0.18/0.52  cnf(c_0_30, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,X1))=X1|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_31, negated_conjecture, (m1_subset_1(k5_lattices(esk9_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_25])).
% 0.18/0.52  cnf(c_0_32, plain, (r2_hidden(X3,a_2_4_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattices(X2,X4,X1)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.52  cnf(c_0_33, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~r1_tarski(X2,X3)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.52  cnf(c_0_34, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0)))=k5_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.52  fof(c_0_35, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.52  fof(c_0_36, plain, ![X32, X33]:(v2_struct_0(X32)|~l3_lattices(X32)|m1_subset_1(k15_lattice3(X32,X33),u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.18/0.52  fof(c_0_37, plain, ![X21, X22, X23, X24, X25]:((~r3_lattice3(X21,X22,X23)|(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_hidden(X24,X23)|r1_lattices(X21,X22,X24)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((m1_subset_1(esk4_3(X21,X22,X25),u1_struct_0(X21))|r3_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((r2_hidden(esk4_3(X21,X22,X25),X25)|r3_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&(~r1_lattices(X21,X22,esk4_3(X21,X22,X25))|r3_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.18/0.52  cnf(c_0_38, plain, (r2_hidden(X1,a_2_4_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattices(X2,X3,X1)|~v4_lattice3(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_32])).
% 0.18/0.52  cnf(c_0_39, negated_conjecture, (r3_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))|~r1_tarski(X1,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_23]), c_0_24]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.52  cnf(c_0_41, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.52  cnf(c_0_42, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.52  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,a_2_4_lattice3(esk9_0,X2))|~r3_lattices(esk9_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_23]), c_0_24]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_44, negated_conjecture, (r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.18/0.52  cnf(c_0_45, negated_conjecture, (m1_subset_1(k15_lattice3(esk9_0,X1),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_21]), c_0_25])).
% 0.18/0.52  fof(c_0_46, plain, ![X39, X40, X41, X42, X43]:(((r3_lattice3(X39,X40,X41)|X40!=k16_lattice3(X39,X41)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)))&(~m1_subset_1(X42,u1_struct_0(X39))|(~r3_lattice3(X39,X42,X41)|r3_lattices(X39,X42,X40))|X40!=k16_lattice3(X39,X41)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39))))&((m1_subset_1(esk8_3(X39,X40,X43),u1_struct_0(X39))|~r3_lattice3(X39,X40,X43)|X40=k16_lattice3(X39,X43)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)))&((r3_lattice3(X39,esk8_3(X39,X40,X43),X43)|~r3_lattice3(X39,X40,X43)|X40=k16_lattice3(X39,X43)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)))&(~r3_lattices(X39,esk8_3(X39,X40,X43),X40)|~r3_lattice3(X39,X40,X43)|X40=k16_lattice3(X39,X43)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.18/0.52  cnf(c_0_47, plain, (X1=k16_lattice3(X2,a_2_4_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.52  fof(c_0_48, plain, ![X6]:(((((((~v2_struct_0(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))&(v4_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v5_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v6_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v7_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v8_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v9_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.18/0.52  fof(c_0_49, plain, ![X16, X18, X19]:(((m1_subset_1(esk2_1(X16),u1_struct_0(X16))|~v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))&((k2_lattices(X16,esk2_1(X16),X18)=esk2_1(X16)|~m1_subset_1(X18,u1_struct_0(X16))|~v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))&(k2_lattices(X16,X18,esk2_1(X16))=esk2_1(X16)|~m1_subset_1(X18,u1_struct_0(X16))|~v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))))&((m1_subset_1(esk3_2(X16,X19),u1_struct_0(X16))|~m1_subset_1(X19,u1_struct_0(X16))|v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))&(k2_lattices(X16,X19,esk3_2(X16,X19))!=X19|k2_lattices(X16,esk3_2(X16,X19),X19)!=X19|~m1_subset_1(X19,u1_struct_0(X16))|v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.18/0.52  cnf(c_0_50, negated_conjecture, (r1_lattices(esk9_0,X1,X2)|~r2_hidden(X2,X3)|~r3_lattice3(esk9_0,X1,X3)|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_21]), c_0_25])).
% 0.18/0.52  cnf(c_0_51, negated_conjecture, (r2_hidden(k5_lattices(esk9_0),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_31])])).
% 0.18/0.52  cnf(c_0_52, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.52  cnf(c_0_53, negated_conjecture, (k16_lattice3(esk9_0,a_2_4_lattice3(esk9_0,X1))=X1|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_23]), c_0_24]), c_0_21])]), c_0_25])).
% 0.18/0.52  fof(c_0_54, plain, ![X27, X28, X29]:((~v6_lattices(X27)|(~m1_subset_1(X28,u1_struct_0(X27))|(~m1_subset_1(X29,u1_struct_0(X27))|k2_lattices(X27,X28,X29)=k2_lattices(X27,X29,X28)))|(v2_struct_0(X27)|~l1_lattices(X27)))&((m1_subset_1(esk5_1(X27),u1_struct_0(X27))|v6_lattices(X27)|(v2_struct_0(X27)|~l1_lattices(X27)))&((m1_subset_1(esk6_1(X27),u1_struct_0(X27))|v6_lattices(X27)|(v2_struct_0(X27)|~l1_lattices(X27)))&(k2_lattices(X27,esk5_1(X27),esk6_1(X27))!=k2_lattices(X27,esk6_1(X27),esk5_1(X27))|v6_lattices(X27)|(v2_struct_0(X27)|~l1_lattices(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.18/0.52  cnf(c_0_55, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.52  fof(c_0_56, plain, ![X7, X8, X9]:(((k2_lattices(X7,X8,X9)=X8|~m1_subset_1(X9,u1_struct_0(X7))|X8!=k5_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~v13_lattices(X7)|(v2_struct_0(X7)|~l1_lattices(X7)))&(k2_lattices(X7,X9,X8)=X8|~m1_subset_1(X9,u1_struct_0(X7))|X8!=k5_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~v13_lattices(X7)|(v2_struct_0(X7)|~l1_lattices(X7))))&((m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))|X8=k5_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~v13_lattices(X7)|(v2_struct_0(X7)|~l1_lattices(X7)))&(k2_lattices(X7,X8,esk1_2(X7,X8))!=X8|k2_lattices(X7,esk1_2(X7,X8),X8)!=X8|X8=k5_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~v13_lattices(X7)|(v2_struct_0(X7)|~l1_lattices(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.18/0.52  cnf(c_0_57, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.52  fof(c_0_58, plain, ![X13, X14, X15]:((~r1_lattices(X13,X14,X15)|k2_lattices(X13,X14,X15)=X14|~m1_subset_1(X15,u1_struct_0(X13))|~m1_subset_1(X14,u1_struct_0(X13))|(v2_struct_0(X13)|~v8_lattices(X13)|~v9_lattices(X13)|~l3_lattices(X13)))&(k2_lattices(X13,X14,X15)!=X14|r1_lattices(X13,X14,X15)|~m1_subset_1(X15,u1_struct_0(X13))|~m1_subset_1(X14,u1_struct_0(X13))|(v2_struct_0(X13)|~v8_lattices(X13)|~v9_lattices(X13)|~l3_lattices(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.18/0.52  cnf(c_0_59, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.52  cnf(c_0_60, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.52  cnf(c_0_61, negated_conjecture, (r1_lattices(esk9_0,X1,k5_lattices(esk9_0))|~r3_lattice3(esk9_0,X1,a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_31])])).
% 0.18/0.52  cnf(c_0_62, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_52])).
% 0.18/0.52  cnf(c_0_63, negated_conjecture, (k16_lattice3(esk9_0,a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,X1)))=k15_lattice3(esk9_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_45])).
% 0.18/0.52  cnf(c_0_64, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.52  cnf(c_0_65, negated_conjecture, (v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_24]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_66, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|X2!=k5_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.18/0.52  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk3_2(esk9_0,X1),u1_struct_0(esk9_0))|v13_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_27]), c_0_25])).
% 0.18/0.52  cnf(c_0_68, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.52  cnf(c_0_69, negated_conjecture, (v9_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_24]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_70, negated_conjecture, (v8_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_24]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_71, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))|~r3_lattice3(esk9_0,k15_lattice3(esk9_0,X1),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_61, c_0_45])).
% 0.18/0.52  cnf(c_0_72, negated_conjecture, (r3_lattice3(esk9_0,k15_lattice3(esk9_0,X1),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_23]), c_0_45]), c_0_24]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_73, negated_conjecture, (k2_lattices(esk9_0,X1,X2)=k2_lattices(esk9_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_27]), c_0_65])]), c_0_25])).
% 0.18/0.52  cnf(c_0_74, plain, (k2_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]), c_0_26])).
% 0.18/0.52  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))|v13_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_67, c_0_45])).
% 0.18/0.52  cnf(c_0_76, negated_conjecture, (r3_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_24]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_77, negated_conjecture, (k2_lattices(esk9_0,X1,X2)=X1|~r1_lattices(esk9_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_78, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.18/0.52  cnf(c_0_79, negated_conjecture, (k2_lattices(esk9_0,X1,k5_lattices(esk9_0))=k2_lattices(esk9_0,k5_lattices(esk9_0),X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_31])).
% 0.18/0.52  cnf(c_0_80, negated_conjecture, (k2_lattices(esk9_0,k5_lattices(esk9_0),X1)=k5_lattices(esk9_0)|m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_27])]), c_0_25])).
% 0.18/0.52  cnf(c_0_81, negated_conjecture, (r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1))), inference(spm,[status(thm)],[c_0_76, c_0_40])).
% 0.18/0.52  cnf(c_0_82, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_31]), c_0_45])])).
% 0.18/0.52  cnf(c_0_83, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))=k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X1))), inference(spm,[status(thm)],[c_0_79, c_0_45])).
% 0.18/0.52  cnf(c_0_84, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.52  cnf(c_0_85, negated_conjecture, (k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X1))=k5_lattices(esk9_0)|m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_80, c_0_45])).
% 0.18/0.52  cnf(c_0_86, negated_conjecture, (r2_hidden(k15_lattice3(esk9_0,X1),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_81]), c_0_45]), c_0_45])])).
% 0.18/0.52  cnf(c_0_87, negated_conjecture, (k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.18/0.52  cnf(c_0_88, negated_conjecture, (r1_lattices(esk9_0,X1,X2)|k2_lattices(esk9_0,X1,X2)!=X1|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_69]), c_0_70]), c_0_21])]), c_0_25])).
% 0.18/0.52  cnf(c_0_89, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X2))=k5_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_85])).
% 0.18/0.52  cnf(c_0_90, negated_conjecture, (v2_struct_0(esk9_0)|~v10_lattices(esk9_0)|~v13_lattices(esk9_0)|~l3_lattices(esk9_0)|k5_lattices(esk9_0)!=k15_lattice3(esk9_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.52  cnf(c_0_91, negated_conjecture, (r1_lattices(esk9_0,X1,k15_lattice3(esk9_0,X2))|~r3_lattice3(esk9_0,X1,a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_86]), c_0_45])])).
% 0.18/0.52  cnf(c_0_92, plain, (m1_subset_1(esk2_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.52  cnf(c_0_93, negated_conjecture, (k15_lattice3(esk9_0,k1_xboole_0)=k5_lattices(esk9_0)|~r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_87]), c_0_45]), c_0_31])])).
% 0.18/0.52  cnf(c_0_94, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_45]), c_0_31])])).
% 0.18/0.52  cnf(c_0_95, negated_conjecture, (k15_lattice3(esk9_0,k1_xboole_0)!=k5_lattices(esk9_0)|~v13_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_21]), c_0_24])]), c_0_25])).
% 0.18/0.52  cnf(c_0_96, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,X2))|~r3_lattice3(esk9_0,k15_lattice3(esk9_0,X1),a_2_4_lattice3(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_91, c_0_45])).
% 0.18/0.52  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))|m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_75]), c_0_27])]), c_0_25])).
% 0.18/0.52  cnf(c_0_98, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|k15_lattice3(esk9_0,k1_xboole_0)=k5_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.18/0.52  cnf(c_0_99, negated_conjecture, (m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))|k15_lattice3(esk9_0,k1_xboole_0)!=k5_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_95, c_0_75])).
% 0.18/0.52  cnf(c_0_100, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.52  cnf(c_0_101, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1))), inference(spm,[status(thm)],[c_0_96, c_0_72])).
% 0.18/0.52  cnf(c_0_102, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_30, c_0_97])).
% 0.18/0.52  cnf(c_0_103, negated_conjecture, (m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_98]), c_0_99])).
% 0.18/0.52  cnf(c_0_104, negated_conjecture, (v13_lattices(esk9_0)|k2_lattices(esk9_0,X1,esk3_2(esk9_0,X1))!=X1|k2_lattices(esk9_0,esk3_2(esk9_0,X1),X1)!=X1|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_27]), c_0_25])).
% 0.18/0.52  cnf(c_0_105, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1))=k15_lattice3(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_101]), c_0_45]), c_0_45])])).
% 0.18/0.52  cnf(c_0_106, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_102])).
% 0.18/0.52  cnf(c_0_107, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))), inference(spm,[status(thm)],[c_0_30, c_0_103])).
% 0.18/0.52  cnf(c_0_108, negated_conjecture, (v13_lattices(esk9_0)|k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))!=k15_lattice3(esk9_0,X1)|k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,X1))!=k15_lattice3(esk9_0,X1)), inference(spm,[status(thm)],[c_0_104, c_0_45])).
% 0.18/0.52  cnf(c_0_109, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))=k15_lattice3(esk9_0,k1_xboole_0)|k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.18/0.52  cnf(c_0_110, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_105]), c_0_45]), c_0_45])])).
% 0.18/0.52  cnf(c_0_111, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_105, c_0_107])).
% 0.18/0.52  cnf(c_0_112, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)|v13_lattices(esk9_0)|k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0))!=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.18/0.52  cnf(c_0_113, negated_conjecture, (k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)|k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_110, c_0_106])).
% 0.18/0.52  cnf(c_0_114, negated_conjecture, (v13_lattices(esk9_0)|k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0))!=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_108, c_0_111])).
% 0.18/0.52  cnf(c_0_115, negated_conjecture, (k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_110, c_0_107])).
% 0.18/0.52  cnf(c_0_116, negated_conjecture, (k2_lattices(esk9_0,X1,k15_lattice3(esk9_0,X2))=k2_lattices(esk9_0,k15_lattice3(esk9_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_45])).
% 0.18/0.52  cnf(c_0_117, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)|v13_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.18/0.52  cnf(c_0_118, plain, (k2_lattices(X1,X2,esk2_1(X1))=esk2_1(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.52  cnf(c_0_119, negated_conjecture, (v13_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115])])).
% 0.18/0.52  cnf(c_0_120, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,X2))=k2_lattices(esk9_0,k15_lattice3(esk9_0,X2),k15_lattice3(esk9_0,X1))), inference(spm,[status(thm)],[c_0_116, c_0_45])).
% 0.18/0.52  cnf(c_0_121, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_117]), c_0_27])]), c_0_25]), c_0_30])).
% 0.18/0.52  cnf(c_0_122, negated_conjecture, (k2_lattices(esk9_0,X1,esk2_1(esk9_0))=esk2_1(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_27])]), c_0_25])).
% 0.18/0.52  cnf(c_0_123, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk2_1(esk9_0))=k2_lattices(esk9_0,esk2_1(esk9_0),k15_lattice3(esk9_0,X1))), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.18/0.52  cnf(c_0_124, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.18/0.52  cnf(c_0_125, negated_conjecture, (k2_lattices(esk9_0,esk2_1(esk9_0),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_110, c_0_121])).
% 0.18/0.52  cnf(c_0_126, negated_conjecture, (k2_lattices(esk9_0,esk2_1(esk9_0),k15_lattice3(esk9_0,X1))=esk2_1(esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_45]), c_0_123])).
% 0.18/0.52  cnf(c_0_127, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_124]), c_0_26])).
% 0.18/0.52  cnf(c_0_128, negated_conjecture, (k15_lattice3(esk9_0,k1_xboole_0)!=k5_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_119])])).
% 0.18/0.52  cnf(c_0_129, negated_conjecture, (k15_lattice3(esk9_0,k1_xboole_0)=esk2_1(esk9_0)), inference(rw,[status(thm)],[c_0_125, c_0_126])).
% 0.18/0.52  cnf(c_0_130, negated_conjecture, (k2_lattices(esk9_0,X1,k5_lattices(esk9_0))=k5_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_119]), c_0_27])]), c_0_25])).
% 0.18/0.52  cnf(c_0_131, negated_conjecture, (m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_45, c_0_121])).
% 0.18/0.52  cnf(c_0_132, negated_conjecture, (k2_lattices(esk9_0,esk2_1(esk9_0),k5_lattices(esk9_0))=k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))), inference(spm,[status(thm)],[c_0_83, c_0_121])).
% 0.18/0.52  cnf(c_0_133, negated_conjecture, (k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_122, c_0_31])).
% 0.18/0.52  cnf(c_0_134, negated_conjecture, (esk2_1(esk9_0)!=k5_lattices(esk9_0)), inference(rw,[status(thm)],[c_0_128, c_0_129])).
% 0.18/0.52  cnf(c_0_135, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_132]), c_0_133]), c_0_134]), ['proof']).
% 0.18/0.52  # SZS output end CNFRefutation
% 0.18/0.52  # Proof object total steps             : 136
% 0.18/0.52  # Proof object clause steps            : 105
% 0.18/0.52  # Proof object formula steps           : 31
% 0.18/0.52  # Proof object conjectures             : 82
% 0.18/0.52  # Proof object clause conjectures      : 79
% 0.18/0.52  # Proof object formula conjectures     : 3
% 0.18/0.52  # Proof object initial clauses used    : 27
% 0.18/0.52  # Proof object initial formulas used   : 15
% 0.18/0.52  # Proof object generating inferences   : 68
% 0.18/0.52  # Proof object simplifying inferences  : 115
% 0.18/0.52  # Training examples: 0 positive, 0 negative
% 0.18/0.53  # Parsed axioms                        : 15
% 0.18/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.53  # Initial clauses                      : 49
% 0.18/0.53  # Removed in clause preprocessing      : 1
% 0.18/0.53  # Initial clauses in saturation        : 48
% 0.18/0.53  # Processed clauses                    : 1461
% 0.18/0.53  # ...of these trivial                  : 51
% 0.18/0.53  # ...subsumed                          : 601
% 0.18/0.53  # ...remaining for further processing  : 809
% 0.18/0.53  # Other redundant clauses eliminated   : 5
% 0.18/0.53  # Clauses deleted for lack of memory   : 0
% 0.18/0.53  # Backward-subsumed                    : 220
% 0.18/0.53  # Backward-rewritten                   : 213
% 0.18/0.53  # Generated clauses                    : 7384
% 0.18/0.53  # ...of the previous two non-trivial   : 7011
% 0.18/0.53  # Contextual simplify-reflections      : 10
% 0.18/0.53  # Paramodulations                      : 7366
% 0.18/0.53  # Factorizations                       : 0
% 0.18/0.53  # Equation resolutions                 : 6
% 0.18/0.53  # Propositional unsat checks           : 0
% 0.18/0.53  #    Propositional check models        : 0
% 0.18/0.53  #    Propositional check unsatisfiable : 0
% 0.18/0.53  #    Propositional clauses             : 0
% 0.18/0.53  #    Propositional clauses after purity: 0
% 0.18/0.53  #    Propositional unsat core size     : 0
% 0.18/0.53  #    Propositional preprocessing time  : 0.000
% 0.18/0.53  #    Propositional encoding time       : 0.000
% 0.18/0.53  #    Propositional solver time         : 0.000
% 0.18/0.53  #    Success case prop preproc time    : 0.000
% 0.18/0.53  #    Success case prop encoding time   : 0.000
% 0.18/0.53  #    Success case prop solver time     : 0.000
% 0.18/0.53  # Current number of processed clauses  : 311
% 0.18/0.53  #    Positive orientable unit clauses  : 91
% 0.18/0.53  #    Positive unorientable unit clauses: 1
% 0.18/0.53  #    Negative unit clauses             : 4
% 0.18/0.53  #    Non-unit-clauses                  : 215
% 0.18/0.53  # Current number of unprocessed clauses: 4795
% 0.18/0.53  # ...number of literals in the above   : 14115
% 0.18/0.53  # Current number of archived formulas  : 0
% 0.18/0.53  # Current number of archived clauses   : 493
% 0.18/0.53  # Clause-clause subsumption calls (NU) : 18372
% 0.18/0.53  # Rec. Clause-clause subsumption calls : 14110
% 0.18/0.53  # Non-unit clause-clause subsumptions  : 669
% 0.18/0.53  # Unit Clause-clause subsumption calls : 2698
% 0.18/0.53  # Rewrite failures with RHS unbound    : 0
% 0.18/0.53  # BW rewrite match attempts            : 380
% 0.18/0.53  # BW rewrite match successes           : 67
% 0.18/0.53  # Condensation attempts                : 0
% 0.18/0.53  # Condensation successes               : 0
% 0.18/0.53  # Termbank termtop insertions          : 173655
% 0.18/0.53  
% 0.18/0.53  # -------------------------------------------------
% 0.18/0.53  # User time                : 0.182 s
% 0.18/0.53  # System time              : 0.012 s
% 0.18/0.53  # Total time               : 0.194 s
% 0.18/0.53  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
