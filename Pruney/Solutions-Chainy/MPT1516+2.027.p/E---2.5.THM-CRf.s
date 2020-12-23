%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:09 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   83 (1446 expanded)
%              Number of clauses        :   54 ( 505 expanded)
%              Number of leaves         :   14 ( 363 expanded)
%              Depth                    :   27
%              Number of atoms          :  503 (9668 expanded)
%              Number of equality atoms :   48 ( 863 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t48_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ~ ( r2_hidden(X4,X2)
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ~ ( r3_lattices(X1,X4,X5)
                          & r2_hidden(X5,X3) ) ) ) )
         => r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(t43_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

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

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X10,X11,X12] :
      ( ( k2_lattices(X10,X11,X12) = X11
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | X11 != k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( k2_lattices(X10,X12,X11) = X11
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | X11 != k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))
        | X11 = k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( k2_lattices(X10,X11,esk1_2(X10,X11)) != X11
        | k2_lattices(X10,esk1_2(X10,X11),X11) != X11
        | X11 = k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_16,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_lattices(X14)
      | m1_subset_1(k5_lattices(X14),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_17,plain,(
    ! [X15] :
      ( ( l1_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( l2_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & v4_lattice3(esk7_0)
    & l3_lattices(esk7_0)
    & ( v2_struct_0(esk7_0)
      | ~ v10_lattices(esk7_0)
      | ~ v13_lattices(esk7_0)
      | ~ l3_lattices(esk7_0)
      | k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_19,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_lattices(X19,X20,X21)
        | k2_lattices(X19,X20,X21) = X20
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v8_lattices(X19)
        | ~ v9_lattices(X19)
        | ~ l3_lattices(X19) )
      & ( k2_lattices(X19,X20,X21) != X20
        | r1_lattices(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v8_lattices(X19)
        | ~ v9_lattices(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_22,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ l3_lattices(X32)
      | m1_subset_1(k15_lattice3(X32,X33),u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_24,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | ~ r1_tarski(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_25,plain,(
    ! [X36,X37,X38,X40] :
      ( ( m1_subset_1(esk6_3(X36,X37,X38),u1_struct_0(X36))
        | r3_lattices(X36,k15_lattice3(X36,X37),k15_lattice3(X36,X38))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) )
      & ( r2_hidden(esk6_3(X36,X37,X38),X37)
        | r3_lattices(X36,k15_lattice3(X36,X37),k15_lattice3(X36,X38))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) )
      & ( ~ m1_subset_1(X40,u1_struct_0(X36))
        | ~ r3_lattices(X36,esk6_3(X36,X37,X38),X40)
        | ~ r2_hidden(X40,X38)
        | r3_lattices(X36,k15_lattice3(X36,X37),k15_lattice3(X36,X38))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( v2_struct_0(esk7_0)
    | ~ v10_lattices(esk7_0)
    | ~ v13_lattices(esk7_0)
    | ~ l3_lattices(esk7_0)
    | k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20])).

cnf(c_0_31,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_37,negated_conjecture,
    ( k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0)
    | ~ v13_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_38,plain,
    ( X1 = k5_lattices(X2)
    | v2_struct_0(X2)
    | ~ r1_lattices(X2,X1,k5_lattices(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v13_lattices(X2)
    | ~ v9_lattices(X2)
    | ~ v8_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_22]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk7_0,X1),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_29])).

fof(c_0_40,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r3_lattices(X16,X17,X18)
        | r1_lattices(X16,X17,X18)
        | v2_struct_0(X16)
        | ~ v6_lattices(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16)) )
      & ( ~ r1_lattices(X16,X17,X18)
        | r3_lattices(X16,X17,X18)
        | v2_struct_0(X16)
        | ~ v6_lattices(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_41,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_tarski(X2,esk6_3(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X34,X35] :
      ( ( k15_lattice3(X34,k6_domain_1(u1_struct_0(X34),X35)) = X35
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ v4_lattice3(X34)
        | ~ l3_lattices(X34) )
      & ( k16_lattice3(X34,k6_domain_1(u1_struct_0(X34),X35)) = X35
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ v4_lattice3(X34)
        | ~ l3_lattices(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0))
    | ~ v13_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_27])]),c_0_29])]),c_0_39])])).

cnf(c_0_45,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_29])).

cnf(c_0_47,plain,
    ( r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( ~ r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0))
    | ~ v13_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_39]),c_0_27])]),c_0_29])).

cnf(c_0_50,plain,
    ( r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( v4_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_52,plain,(
    ! [X22,X24,X25] :
      ( ( m1_subset_1(esk2_1(X22),u1_struct_0(X22))
        | ~ v13_lattices(X22)
        | v2_struct_0(X22)
        | ~ l1_lattices(X22) )
      & ( k2_lattices(X22,esk2_1(X22),X24) = esk2_1(X22)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ v13_lattices(X22)
        | v2_struct_0(X22)
        | ~ l1_lattices(X22) )
      & ( k2_lattices(X22,X24,esk2_1(X22)) = esk2_1(X22)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ v13_lattices(X22)
        | v2_struct_0(X22)
        | ~ l1_lattices(X22) )
      & ( m1_subset_1(esk3_2(X22,X25),u1_struct_0(X22))
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | v13_lattices(X22)
        | v2_struct_0(X22)
        | ~ l1_lattices(X22) )
      & ( k2_lattices(X22,X25,esk3_2(X22,X25)) != X25
        | k2_lattices(X22,esk3_2(X22,X25),X25) != X25
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | v13_lattices(X22)
        | v2_struct_0(X22)
        | ~ l1_lattices(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( ~ v13_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_46]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29])).

fof(c_0_56,plain,(
    ! [X9] :
      ( ( ~ v2_struct_0(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v4_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v5_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v6_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v7_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v9_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_27])])).

cnf(c_0_58,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_60,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_63,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ r1_lattices(X1,X2,esk3_2(X1,X2))
    | ~ m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_31]),c_0_22])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_66,negated_conjecture,
    ( v13_lattices(esk7_0)
    | k2_lattices(esk7_0,esk3_2(esk7_0,X1),X1) != X1
    | ~ r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_27])]),c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( v13_lattices(esk7_0)
    | k2_lattices(esk7_0,esk3_2(esk7_0,X1),X1) != X1
    | ~ r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v8_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_58]),c_0_28]),c_0_27])]),c_0_29])).

fof(c_0_68,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v6_lattices(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | k2_lattices(X27,X28,X29) = k2_lattices(X27,X29,X28)
        | v2_struct_0(X27)
        | ~ l1_lattices(X27) )
      & ( m1_subset_1(esk4_1(X27),u1_struct_0(X27))
        | v6_lattices(X27)
        | v2_struct_0(X27)
        | ~ l1_lattices(X27) )
      & ( m1_subset_1(esk5_1(X27),u1_struct_0(X27))
        | v6_lattices(X27)
        | v2_struct_0(X27)
        | ~ l1_lattices(X27) )
      & ( k2_lattices(X27,esk4_1(X27),esk5_1(X27)) != k2_lattices(X27,esk5_1(X27),esk4_1(X27))
        | v6_lattices(X27)
        | v2_struct_0(X27)
        | ~ l1_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_69,negated_conjecture,
    ( v13_lattices(esk7_0)
    | k2_lattices(esk7_0,esk3_2(esk7_0,X1),X1) != X1
    | ~ r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_60]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_70,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( v13_lattices(esk7_0)
    | k2_lattices(esk7_0,X1,esk3_2(esk7_0,X1)) != X1
    | ~ r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_29]),c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( v13_lattices(esk7_0)
    | k2_lattices(esk7_0,X1,esk3_2(esk7_0,X1)) != X1
    | ~ r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v6_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_22]),c_0_27])])).

cnf(c_0_73,negated_conjecture,
    ( v13_lattices(esk7_0)
    | k2_lattices(esk7_0,X1,esk3_2(esk7_0,X1)) != X1
    | ~ r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_63]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_74,negated_conjecture,
    ( v13_lattices(esk7_0)
    | ~ r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_31]),c_0_27])]),c_0_29]),c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( v13_lattices(esk7_0)
    | ~ r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v8_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_58]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( v13_lattices(esk7_0)
    | ~ r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_60]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( ~ r3_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_45]),c_0_27])]),c_0_29]),c_0_65]),c_0_53])).

cnf(c_0_78,negated_conjecture,
    ( ~ r3_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_58]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_79,negated_conjecture,
    ( ~ r3_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_60]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_80,negated_conjecture,
    ( ~ r3_lattices(esk7_0,X1,esk3_2(esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_63]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_81,negated_conjecture,
    ( ~ m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_50]),c_0_39]),c_0_51]),c_0_28]),c_0_27])]),c_0_29])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_65]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:57:12 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.46/0.64  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.46/0.64  # and selection function PSelectUnlessUniqMaxPos.
% 0.46/0.64  #
% 0.46/0.64  # Preprocessing time       : 0.030 s
% 0.46/0.64  # Presaturation interreduction done
% 0.46/0.64  
% 0.46/0.64  # Proof found!
% 0.46/0.64  # SZS status Theorem
% 0.46/0.64  # SZS output start CNFRefutation
% 0.46/0.64  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 0.46/0.64  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.46/0.64  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.46/0.64  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.46/0.64  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.46/0.64  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.46/0.64  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.46/0.64  fof(t48_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 0.46/0.64  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.46/0.64  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.46/0.64  fof(t43_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattice3)).
% 0.46/0.64  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 0.46/0.64  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.46/0.64  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.46/0.64  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.46/0.64  fof(c_0_15, plain, ![X10, X11, X12]:(((k2_lattices(X10,X11,X12)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X12,X11)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))&((m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X11,esk1_2(X10,X11))!=X11|k2_lattices(X10,esk1_2(X10,X11),X11)!=X11|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.46/0.64  fof(c_0_16, plain, ![X14]:(v2_struct_0(X14)|~l1_lattices(X14)|m1_subset_1(k5_lattices(X14),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.46/0.64  fof(c_0_17, plain, ![X15]:((l1_lattices(X15)|~l3_lattices(X15))&(l2_lattices(X15)|~l3_lattices(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.46/0.64  fof(c_0_18, negated_conjecture, ((((~v2_struct_0(esk7_0)&v10_lattices(esk7_0))&v4_lattice3(esk7_0))&l3_lattices(esk7_0))&(v2_struct_0(esk7_0)|~v10_lattices(esk7_0)|~v13_lattices(esk7_0)|~l3_lattices(esk7_0)|k5_lattices(esk7_0)!=k15_lattice3(esk7_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.46/0.64  cnf(c_0_19, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.64  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.64  fof(c_0_21, plain, ![X19, X20, X21]:((~r1_lattices(X19,X20,X21)|k2_lattices(X19,X20,X21)=X20|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v8_lattices(X19)|~v9_lattices(X19)|~l3_lattices(X19)))&(k2_lattices(X19,X20,X21)!=X20|r1_lattices(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v8_lattices(X19)|~v9_lattices(X19)|~l3_lattices(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.46/0.64  cnf(c_0_22, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.64  fof(c_0_23, plain, ![X32, X33]:(v2_struct_0(X32)|~l3_lattices(X32)|m1_subset_1(k15_lattice3(X32,X33),u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.46/0.64  fof(c_0_24, plain, ![X7, X8]:(~r2_hidden(X7,X8)|~r1_tarski(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.46/0.64  fof(c_0_25, plain, ![X36, X37, X38, X40]:((m1_subset_1(esk6_3(X36,X37,X38),u1_struct_0(X36))|r3_lattices(X36,k15_lattice3(X36,X37),k15_lattice3(X36,X38))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))&((r2_hidden(esk6_3(X36,X37,X38),X37)|r3_lattices(X36,k15_lattice3(X36,X37),k15_lattice3(X36,X38))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))&(~m1_subset_1(X40,u1_struct_0(X36))|(~r3_lattices(X36,esk6_3(X36,X37,X38),X40)|~r2_hidden(X40,X38))|r3_lattices(X36,k15_lattice3(X36,X37),k15_lattice3(X36,X38))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).
% 0.46/0.64  cnf(c_0_26, negated_conjecture, (v2_struct_0(esk7_0)|~v10_lattices(esk7_0)|~v13_lattices(esk7_0)|~l3_lattices(esk7_0)|k5_lattices(esk7_0)!=k15_lattice3(esk7_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  cnf(c_0_27, negated_conjecture, (l3_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  cnf(c_0_28, negated_conjecture, (v10_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  cnf(c_0_30, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_20])).
% 0.46/0.64  cnf(c_0_31, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.64  cnf(c_0_32, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 0.46/0.64  cnf(c_0_33, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.46/0.64  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.64  cnf(c_0_35, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.46/0.64  fof(c_0_36, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.46/0.64  cnf(c_0_37, negated_conjecture, (k5_lattices(esk7_0)!=k15_lattice3(esk7_0,k1_xboole_0)|~v13_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])]), c_0_29])).
% 0.46/0.64  cnf(c_0_38, plain, (X1=k5_lattices(X2)|v2_struct_0(X2)|~r1_lattices(X2,X1,k5_lattices(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v13_lattices(X2)|~v9_lattices(X2)|~v8_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_22]), c_0_32])).
% 0.46/0.64  cnf(c_0_39, negated_conjecture, (m1_subset_1(k15_lattice3(esk7_0,X1),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_27]), c_0_29])).
% 0.46/0.64  fof(c_0_40, plain, ![X16, X17, X18]:((~r3_lattices(X16,X17,X18)|r1_lattices(X16,X17,X18)|(v2_struct_0(X16)|~v6_lattices(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))))&(~r1_lattices(X16,X17,X18)|r3_lattices(X16,X17,X18)|(v2_struct_0(X16)|~v6_lattices(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.46/0.64  cnf(c_0_41, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_tarski(X2,esk6_3(X1,X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.46/0.64  cnf(c_0_42, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.46/0.64  fof(c_0_43, plain, ![X34, X35]:((k15_lattice3(X34,k6_domain_1(u1_struct_0(X34),X35))=X35|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))&(k16_lattice3(X34,k6_domain_1(u1_struct_0(X34),X35))=X35|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).
% 0.46/0.64  cnf(c_0_44, negated_conjecture, (~r1_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0))|~v13_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_27])]), c_0_29])]), c_0_39])])).
% 0.46/0.64  cnf(c_0_45, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.46/0.64  cnf(c_0_46, negated_conjecture, (m1_subset_1(k5_lattices(esk7_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_29])).
% 0.46/0.64  cnf(c_0_47, plain, (r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.46/0.64  cnf(c_0_48, plain, (k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.46/0.64  cnf(c_0_49, negated_conjecture, (~r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0))|~v13_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_39]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_50, plain, (r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.46/0.64  cnf(c_0_51, negated_conjecture, (v4_lattice3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  fof(c_0_52, plain, ![X22, X24, X25]:(((m1_subset_1(esk2_1(X22),u1_struct_0(X22))|~v13_lattices(X22)|(v2_struct_0(X22)|~l1_lattices(X22)))&((k2_lattices(X22,esk2_1(X22),X24)=esk2_1(X22)|~m1_subset_1(X24,u1_struct_0(X22))|~v13_lattices(X22)|(v2_struct_0(X22)|~l1_lattices(X22)))&(k2_lattices(X22,X24,esk2_1(X22))=esk2_1(X22)|~m1_subset_1(X24,u1_struct_0(X22))|~v13_lattices(X22)|(v2_struct_0(X22)|~l1_lattices(X22)))))&((m1_subset_1(esk3_2(X22,X25),u1_struct_0(X22))|~m1_subset_1(X25,u1_struct_0(X22))|v13_lattices(X22)|(v2_struct_0(X22)|~l1_lattices(X22)))&(k2_lattices(X22,X25,esk3_2(X22,X25))!=X25|k2_lattices(X22,esk3_2(X22,X25),X25)!=X25|~m1_subset_1(X25,u1_struct_0(X22))|v13_lattices(X22)|(v2_struct_0(X22)|~l1_lattices(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.46/0.64  cnf(c_0_53, negated_conjecture, (~v13_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_46]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_54, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.46/0.64  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29])).
% 0.46/0.64  fof(c_0_56, plain, ![X9]:(((((((~v2_struct_0(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))&(v4_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v5_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v6_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v7_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v8_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v9_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.46/0.64  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_22]), c_0_27])])).
% 0.46/0.64  cnf(c_0_58, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.46/0.64  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_60, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.46/0.64  cnf(c_0_61, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.46/0.64  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_63, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.46/0.64  cnf(c_0_64, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~r1_lattices(X1,X2,esk3_2(X1,X2))|~m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_31]), c_0_22])).
% 0.46/0.64  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_66, negated_conjecture, (v13_lattices(esk7_0)|k2_lattices(esk7_0,esk3_2(esk7_0,X1),X1)!=X1|~r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_67, negated_conjecture, (v13_lattices(esk7_0)|k2_lattices(esk7_0,esk3_2(esk7_0,X1),X1)!=X1|~r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v8_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_58]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  fof(c_0_68, plain, ![X27, X28, X29]:((~v6_lattices(X27)|(~m1_subset_1(X28,u1_struct_0(X27))|(~m1_subset_1(X29,u1_struct_0(X27))|k2_lattices(X27,X28,X29)=k2_lattices(X27,X29,X28)))|(v2_struct_0(X27)|~l1_lattices(X27)))&((m1_subset_1(esk4_1(X27),u1_struct_0(X27))|v6_lattices(X27)|(v2_struct_0(X27)|~l1_lattices(X27)))&((m1_subset_1(esk5_1(X27),u1_struct_0(X27))|v6_lattices(X27)|(v2_struct_0(X27)|~l1_lattices(X27)))&(k2_lattices(X27,esk4_1(X27),esk5_1(X27))!=k2_lattices(X27,esk5_1(X27),esk4_1(X27))|v6_lattices(X27)|(v2_struct_0(X27)|~l1_lattices(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.46/0.64  cnf(c_0_69, negated_conjecture, (v13_lattices(esk7_0)|k2_lattices(esk7_0,esk3_2(esk7_0,X1),X1)!=X1|~r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_60]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_70, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.46/0.64  cnf(c_0_71, negated_conjecture, (v13_lattices(esk7_0)|k2_lattices(esk7_0,X1,esk3_2(esk7_0,X1))!=X1|~r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_29]), c_0_65])).
% 0.46/0.64  cnf(c_0_72, negated_conjecture, (v13_lattices(esk7_0)|k2_lattices(esk7_0,X1,esk3_2(esk7_0,X1))!=X1|~r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v6_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_22]), c_0_27])])).
% 0.46/0.64  cnf(c_0_73, negated_conjecture, (v13_lattices(esk7_0)|k2_lattices(esk7_0,X1,esk3_2(esk7_0,X1))!=X1|~r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_63]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_74, negated_conjecture, (v13_lattices(esk7_0)|~r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_31]), c_0_27])]), c_0_29]), c_0_65])).
% 0.46/0.64  cnf(c_0_75, negated_conjecture, (v13_lattices(esk7_0)|~r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v8_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_58]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_76, negated_conjecture, (v13_lattices(esk7_0)|~r1_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_60]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_77, negated_conjecture, (~r3_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_45]), c_0_27])]), c_0_29]), c_0_65]), c_0_53])).
% 0.46/0.64  cnf(c_0_78, negated_conjecture, (~r3_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_58]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_79, negated_conjecture, (~r3_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_60]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_80, negated_conjecture, (~r3_lattices(esk7_0,X1,esk3_2(esk7_0,X1))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_63]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_81, negated_conjecture, (~m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_50]), c_0_39]), c_0_51]), c_0_28]), c_0_27])]), c_0_29])).
% 0.46/0.64  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_65]), c_0_39])]), ['proof']).
% 0.46/0.64  # SZS output end CNFRefutation
% 0.46/0.64  # Proof object total steps             : 83
% 0.46/0.64  # Proof object clause steps            : 54
% 0.46/0.64  # Proof object formula steps           : 29
% 0.46/0.64  # Proof object conjectures             : 34
% 0.46/0.64  # Proof object clause conjectures      : 31
% 0.46/0.64  # Proof object formula conjectures     : 3
% 0.46/0.64  # Proof object initial clauses used    : 21
% 0.46/0.64  # Proof object initial formulas used   : 14
% 0.46/0.64  # Proof object generating inferences   : 31
% 0.46/0.64  # Proof object simplifying inferences  : 99
% 0.46/0.64  # Training examples: 0 positive, 0 negative
% 0.46/0.64  # Parsed axioms                        : 14
% 0.46/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.64  # Initial clauses                      : 40
% 0.46/0.64  # Removed in clause preprocessing      : 1
% 0.46/0.64  # Initial clauses in saturation        : 39
% 0.46/0.64  # Processed clauses                    : 968
% 0.46/0.64  # ...of these trivial                  : 0
% 0.46/0.64  # ...subsumed                          : 433
% 0.46/0.64  # ...remaining for further processing  : 535
% 0.46/0.64  # Other redundant clauses eliminated   : 382
% 0.46/0.64  # Clauses deleted for lack of memory   : 0
% 0.46/0.64  # Backward-subsumed                    : 137
% 0.46/0.64  # Backward-rewritten                   : 0
% 0.46/0.64  # Generated clauses                    : 12864
% 0.46/0.64  # ...of the previous two non-trivial   : 12265
% 0.46/0.64  # Contextual simplify-reflections      : 30
% 0.46/0.64  # Paramodulations                      : 12478
% 0.46/0.64  # Factorizations                       : 4
% 0.46/0.64  # Equation resolutions                 : 382
% 0.46/0.64  # Propositional unsat checks           : 0
% 0.46/0.64  #    Propositional check models        : 0
% 0.46/0.64  #    Propositional check unsatisfiable : 0
% 0.46/0.64  #    Propositional clauses             : 0
% 0.46/0.64  #    Propositional clauses after purity: 0
% 0.46/0.64  #    Propositional unsat core size     : 0
% 0.46/0.64  #    Propositional preprocessing time  : 0.000
% 0.46/0.64  #    Propositional encoding time       : 0.000
% 0.46/0.64  #    Propositional solver time         : 0.000
% 0.46/0.64  #    Success case prop preproc time    : 0.000
% 0.46/0.64  #    Success case prop encoding time   : 0.000
% 0.46/0.64  #    Success case prop solver time     : 0.000
% 0.46/0.64  # Current number of processed clauses  : 357
% 0.46/0.64  #    Positive orientable unit clauses  : 6
% 0.46/0.64  #    Positive unorientable unit clauses: 0
% 0.46/0.64  #    Negative unit clauses             : 2
% 0.46/0.64  #    Non-unit-clauses                  : 349
% 0.46/0.64  # Current number of unprocessed clauses: 11286
% 0.46/0.64  # ...number of literals in the above   : 141871
% 0.46/0.64  # Current number of archived formulas  : 0
% 0.46/0.64  # Current number of archived clauses   : 176
% 0.46/0.64  # Clause-clause subsumption calls (NU) : 67565
% 0.46/0.64  # Rec. Clause-clause subsumption calls : 3503
% 0.46/0.64  # Non-unit clause-clause subsumptions  : 598
% 0.46/0.64  # Unit Clause-clause subsumption calls : 45
% 0.46/0.64  # Rewrite failures with RHS unbound    : 0
% 0.46/0.64  # BW rewrite match attempts            : 0
% 0.46/0.64  # BW rewrite match successes           : 0
% 0.46/0.64  # Condensation attempts                : 0
% 0.46/0.64  # Condensation successes               : 0
% 0.46/0.64  # Termbank termtop insertions          : 478226
% 0.46/0.64  
% 0.46/0.64  # -------------------------------------------------
% 0.46/0.64  # User time                : 0.297 s
% 0.46/0.64  # System time              : 0.012 s
% 0.46/0.64  # Total time               : 0.309 s
% 0.46/0.64  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
