%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 (1336 expanded)
%              Number of clauses        :   63 ( 485 expanded)
%              Number of leaves         :   16 ( 328 expanded)
%              Depth                    :   16
%              Number of atoms          :  520 (8550 expanded)
%              Number of equality atoms :   65 ( 834 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(d17_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r4_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

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

fof(d21_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ( X3 = k15_lattice3(X1,X2)
            <=> ( r4_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r4_lattice3(X1,X4,X2)
                     => r1_lattices(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

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

fof(c_0_16,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r1_xboole_0(X12,X13)
        | r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X17,k3_xboole_0(X15,X16))
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X18] :
      ( ~ r1_tarski(X18,k1_xboole_0)
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X51,X52] :
      ( v2_struct_0(X51)
      | ~ l3_lattices(X51)
      | m1_subset_1(k15_lattice3(X51,X52),u1_struct_0(X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk12_0)
    & v10_lattices(esk12_0)
    & v4_lattice3(esk12_0)
    & l3_lattices(esk12_0)
    & ( v2_struct_0(esk12_0)
      | ~ v10_lattices(esk12_0)
      | ~ v13_lattices(esk12_0)
      | ~ l3_lattices(esk12_0)
      | k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_26,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ( ~ r4_lattice3(X35,X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | ~ r2_hidden(X38,X37)
        | r1_lattices(X35,X38,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ l3_lattices(X35) )
      & ( m1_subset_1(esk6_3(X35,X36,X39),u1_struct_0(X35))
        | r4_lattice3(X35,X36,X39)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ l3_lattices(X35) )
      & ( r2_hidden(esk6_3(X35,X36,X39),X39)
        | r4_lattice3(X35,X36,X39)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ l3_lattices(X35) )
      & ( ~ r1_lattices(X35,esk6_3(X35,X36,X39),X36)
        | r4_lattice3(X35,X36,X39)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ l3_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( l3_lattices(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X30,X32,X33] :
      ( ( m1_subset_1(esk4_1(X30),u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,esk4_1(X30),X32) = esk4_1(X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,X32,esk4_1(X30)) = esk4_1(X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( m1_subset_1(esk5_2(X30,X33),u1_struct_0(X30))
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,X33,esk5_2(X30,X33)) != X33
        | k2_lattices(X30,esk5_2(X30,X33),X33) != X33
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

fof(c_0_31,plain,(
    ! [X41,X42,X43,X44] :
      ( ( r4_lattice3(X41,X43,X42)
        | X43 != k15_lattice3(X41,X42)
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ v10_lattices(X41)
        | ~ v4_lattice3(X41)
        | ~ l3_lattices(X41)
        | v2_struct_0(X41)
        | ~ l3_lattices(X41) )
      & ( ~ m1_subset_1(X44,u1_struct_0(X41))
        | ~ r4_lattice3(X41,X44,X42)
        | r1_lattices(X41,X43,X44)
        | X43 != k15_lattice3(X41,X42)
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ v10_lattices(X41)
        | ~ v4_lattice3(X41)
        | ~ l3_lattices(X41)
        | v2_struct_0(X41)
        | ~ l3_lattices(X41) )
      & ( m1_subset_1(esk7_3(X41,X42,X43),u1_struct_0(X41))
        | ~ r4_lattice3(X41,X43,X42)
        | X43 = k15_lattice3(X41,X42)
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ v10_lattices(X41)
        | ~ v4_lattice3(X41)
        | ~ l3_lattices(X41)
        | v2_struct_0(X41)
        | ~ l3_lattices(X41) )
      & ( r4_lattice3(X41,esk7_3(X41,X42,X43),X42)
        | ~ r4_lattice3(X41,X43,X42)
        | X43 = k15_lattice3(X41,X42)
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ v10_lattices(X41)
        | ~ v4_lattice3(X41)
        | ~ l3_lattices(X41)
        | v2_struct_0(X41)
        | ~ l3_lattices(X41) )
      & ( ~ r1_lattices(X41,X43,esk7_3(X41,X42,X43))
        | ~ r4_lattice3(X41,X43,X42)
        | X43 = k15_lattice3(X41,X42)
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | v2_struct_0(X41)
        | ~ v10_lattices(X41)
        | ~ v4_lattice3(X41)
        | ~ l3_lattices(X41)
        | v2_struct_0(X41)
        | ~ l3_lattices(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk12_0,X1),u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X26] :
      ( ( l1_lattices(X26)
        | ~ l3_lattices(X26) )
      & ( l2_lattices(X26)
        | ~ l3_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_37,plain,
    ( r1_lattices(X2,X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | X4 != k15_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),X2)
    | r2_hidden(esk6_3(esk12_0,k15_lattice3(esk12_0,X1),X2),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28])]),c_0_29])).

fof(c_0_40,plain,(
    ! [X19] : r1_xboole_0(X19,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_41,plain,(
    ! [X61,X62] :
      ( ( k15_lattice3(X61,k6_domain_1(u1_struct_0(X61),X62)) = X62
        | ~ m1_subset_1(X62,u1_struct_0(X61))
        | v2_struct_0(X61)
        | ~ v10_lattices(X61)
        | ~ v4_lattice3(X61)
        | ~ l3_lattices(X61) )
      & ( k16_lattice3(X61,k6_domain_1(u1_struct_0(X61),X62)) = X62
        | ~ m1_subset_1(X62,u1_struct_0(X61))
        | v2_struct_0(X61)
        | ~ v10_lattices(X61)
        | ~ v4_lattice3(X61)
        | ~ l3_lattices(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),u1_struct_0(esk12_0))
    | v13_lattices(esk12_0)
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_29])).

cnf(c_0_43,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X20] :
      ( ( ~ v2_struct_0(X20)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( v4_lattices(X20)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( v5_lattices(X20)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( v6_lattices(X20)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( v7_lattices(X20)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( v8_lattices(X20)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( v9_lattices(X20)
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),u1_struct_0(esk12_0))
    | v13_lattices(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28])])).

cnf(c_0_50,negated_conjecture,
    ( v4_lattice3(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( v10_lattices(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_52,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l1_lattices(X25)
      | m1_subset_1(k5_lattices(X25),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_53,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_lattices(X27,X28,X29)
        | k2_lattices(X27,X28,X29) = X28
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v8_lattices(X27)
        | ~ v9_lattices(X27)
        | ~ l3_lattices(X27) )
      & ( k2_lattices(X27,X28,X29) != X28
        | r1_lattices(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v8_lattices(X27)
        | ~ v9_lattices(X27)
        | ~ l3_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_54,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( k15_lattice3(esk12_0,k6_domain_1(u1_struct_0(esk12_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1)))) = esk5_2(esk12_0,k15_lattice3(esk12_0,X1))
    | v13_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_28])]),c_0_29])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( v9_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_28])]),c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( v8_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_51]),c_0_28])]),c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattices(esk12_0,k15_lattice3(esk12_0,X1),esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))
    | v13_lattices(esk12_0)
    | ~ r4_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_49]),c_0_50]),c_0_51]),c_0_28])]),c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( r4_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),k1_xboole_0)
    | v13_lattices(esk12_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_43])).

cnf(c_0_66,negated_conjecture,
    ( k2_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2))) = X1
    | v13_lattices(esk12_0)
    | ~ r1_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_49]),c_0_61]),c_0_62]),c_0_28])]),c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1)))
    | v13_lattices(esk12_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_68,plain,(
    ! [X21,X22,X23] :
      ( ( k2_lattices(X21,X22,X23) = X22
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | X22 != k5_lattices(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v13_lattices(X21)
        | v2_struct_0(X21)
        | ~ l1_lattices(X21) )
      & ( k2_lattices(X21,X23,X22) = X22
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | X22 != k5_lattices(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v13_lattices(X21)
        | v2_struct_0(X21)
        | ~ l1_lattices(X21) )
      & ( m1_subset_1(esk3_2(X21,X22),u1_struct_0(X21))
        | X22 = k5_lattices(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v13_lattices(X21)
        | v2_struct_0(X21)
        | ~ l1_lattices(X21) )
      & ( k2_lattices(X21,X22,esk3_2(X21,X22)) != X22
        | k2_lattices(X21,esk3_2(X21,X22),X22) != X22
        | X22 = k5_lattices(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ v13_lattices(X21)
        | v2_struct_0(X21)
        | ~ l1_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk12_0),u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_28]),c_0_29])).

cnf(c_0_70,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk5_2(X1,X2)) != X2
    | k2_lattices(X1,esk5_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_71,negated_conjecture,
    ( k2_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1))) = k15_lattice3(esk12_0,k1_xboole_0)
    | v13_lattices(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_34])])).

fof(c_0_72,plain,(
    ! [X46,X47,X48] :
      ( ( ~ v6_lattices(X46)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | k2_lattices(X46,X47,X48) = k2_lattices(X46,X48,X47)
        | v2_struct_0(X46)
        | ~ l1_lattices(X46) )
      & ( m1_subset_1(esk8_1(X46),u1_struct_0(X46))
        | v6_lattices(X46)
        | v2_struct_0(X46)
        | ~ l1_lattices(X46) )
      & ( m1_subset_1(esk9_1(X46),u1_struct_0(X46))
        | v6_lattices(X46)
        | v2_struct_0(X46)
        | ~ l1_lattices(X46) )
      & ( k2_lattices(X46,esk8_1(X46),esk9_1(X46)) != k2_lattices(X46,esk9_1(X46),esk8_1(X46))
        | v6_lattices(X46)
        | v2_struct_0(X46)
        | ~ l1_lattices(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_73,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_74,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k2_lattices(esk12_0,X1,k5_lattices(esk12_0)) = X1
    | ~ r1_lattices(esk12_0,X1,k5_lattices(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_69]),c_0_61]),c_0_62]),c_0_28])]),c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0))
    | ~ r4_lattice3(esk12_0,k5_lattices(esk12_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_69]),c_0_50]),c_0_51]),c_0_28])]),c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( v13_lattices(esk12_0)
    | k2_lattices(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)),k15_lattice3(esk12_0,k1_xboole_0)) != k15_lattice3(esk12_0,k1_xboole_0)
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_34])]),c_0_29])).

cnf(c_0_78,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( v6_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_51]),c_0_28])]),c_0_29])).

cnf(c_0_80,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_59])).

cnf(c_0_81,negated_conjecture,
    ( k2_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0)) = k15_lattice3(esk12_0,X1)
    | ~ r4_lattice3(esk12_0,k5_lattices(esk12_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_34])])).

cnf(c_0_82,negated_conjecture,
    ( v13_lattices(esk12_0)
    | k2_lattices(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)),k15_lattice3(esk12_0,k1_xboole_0)) != k15_lattice3(esk12_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_43]),c_0_28])])).

cnf(c_0_83,negated_conjecture,
    ( k2_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2)) = k2_lattices(esk12_0,k15_lattice3(esk12_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_34]),c_0_79])]),c_0_29])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(esk12_0)
    | ~ v10_lattices(esk12_0)
    | ~ v13_lattices(esk12_0)
    | ~ l3_lattices(esk12_0)
    | k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_85,negated_conjecture,
    ( k15_lattice3(esk12_0,X1) = k5_lattices(esk12_0)
    | ~ r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)
    | ~ v13_lattices(esk12_0)
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_34])]),c_0_29])).

cnf(c_0_86,negated_conjecture,
    ( v13_lattices(esk12_0)
    | ~ l1_lattices(esk12_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_49]),c_0_71])).

cnf(c_0_87,negated_conjecture,
    ( r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)
    | r2_hidden(esk6_3(esk12_0,k5_lattices(esk12_0),X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_69]),c_0_28])]),c_0_29])).

cnf(c_0_88,negated_conjecture,
    ( k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0)
    | ~ v13_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_28]),c_0_51])]),c_0_29])).

cnf(c_0_89,negated_conjecture,
    ( k15_lattice3(esk12_0,X1) = k5_lattices(esk12_0)
    | ~ r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)
    | ~ l1_lattices(esk12_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( r4_lattice3(esk12_0,k5_lattices(esk12_0),k1_xboole_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0)
    | ~ l1_lattices(esk12_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k15_lattice3(esk12_0,X1) = k5_lattices(esk12_0)
    | ~ r4_lattice3(esk12_0,k5_lattices(esk12_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_43]),c_0_28])])).

cnf(c_0_93,negated_conjecture,
    ( r4_lattice3(esk12_0,k5_lattices(esk12_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_47])).

cnf(c_0_94,negated_conjecture,
    ( k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_43]),c_0_28])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:56:02 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.19/0.53  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.19/0.53  #
% 0.19/0.53  # Preprocessing time       : 0.031 s
% 0.19/0.53  # Presaturation interreduction done
% 0.19/0.53  
% 0.19/0.53  # Proof found!
% 0.19/0.53  # SZS status Theorem
% 0.19/0.53  # SZS output start CNFRefutation
% 0.19/0.53  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.53  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 0.19/0.53  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.53  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.19/0.53  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.19/0.53  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 0.19/0.53  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.19/0.53  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.53  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.53  fof(t43_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattice3)).
% 0.19/0.53  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.53  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.19/0.53  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.19/0.53  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.19/0.53  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.19/0.53  fof(c_0_16, plain, ![X12, X13, X15, X16, X17]:((r1_xboole_0(X12,X13)|r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)))&(~r2_hidden(X17,k3_xboole_0(X15,X16))|~r1_xboole_0(X15,X16))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.53  fof(c_0_17, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.53  fof(c_0_18, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.19/0.53  fof(c_0_19, plain, ![X18]:(~r1_tarski(X18,k1_xboole_0)|X18=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.53  cnf(c_0_20, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.53  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  fof(c_0_22, plain, ![X51, X52]:(v2_struct_0(X51)|~l3_lattices(X51)|m1_subset_1(k15_lattice3(X51,X52),u1_struct_0(X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.19/0.53  fof(c_0_23, negated_conjecture, ((((~v2_struct_0(esk12_0)&v10_lattices(esk12_0))&v4_lattice3(esk12_0))&l3_lattices(esk12_0))&(v2_struct_0(esk12_0)|~v10_lattices(esk12_0)|~v13_lattices(esk12_0)|~l3_lattices(esk12_0)|k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.19/0.53  cnf(c_0_24, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.53  cnf(c_0_25, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.53  fof(c_0_26, plain, ![X35, X36, X37, X38, X39]:((~r4_lattice3(X35,X36,X37)|(~m1_subset_1(X38,u1_struct_0(X35))|(~r2_hidden(X38,X37)|r1_lattices(X35,X38,X36)))|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~l3_lattices(X35)))&((m1_subset_1(esk6_3(X35,X36,X39),u1_struct_0(X35))|r4_lattice3(X35,X36,X39)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~l3_lattices(X35)))&((r2_hidden(esk6_3(X35,X36,X39),X39)|r4_lattice3(X35,X36,X39)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~l3_lattices(X35)))&(~r1_lattices(X35,esk6_3(X35,X36,X39),X36)|r4_lattice3(X35,X36,X39)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~l3_lattices(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.19/0.53  cnf(c_0_27, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.53  cnf(c_0_28, negated_conjecture, (l3_lattices(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.53  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.53  fof(c_0_30, plain, ![X30, X32, X33]:(((m1_subset_1(esk4_1(X30),u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&((k2_lattices(X30,esk4_1(X30),X32)=esk4_1(X30)|~m1_subset_1(X32,u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,X32,esk4_1(X30))=esk4_1(X30)|~m1_subset_1(X32,u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))))&((m1_subset_1(esk5_2(X30,X33),u1_struct_0(X30))|~m1_subset_1(X33,u1_struct_0(X30))|v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,X33,esk5_2(X30,X33))!=X33|k2_lattices(X30,esk5_2(X30,X33),X33)!=X33|~m1_subset_1(X33,u1_struct_0(X30))|v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.19/0.53  fof(c_0_31, plain, ![X41, X42, X43, X44]:(((r4_lattice3(X41,X43,X42)|X43!=k15_lattice3(X41,X42)|~m1_subset_1(X43,u1_struct_0(X41))|(v2_struct_0(X41)|~v10_lattices(X41)|~v4_lattice3(X41)|~l3_lattices(X41))|(v2_struct_0(X41)|~l3_lattices(X41)))&(~m1_subset_1(X44,u1_struct_0(X41))|(~r4_lattice3(X41,X44,X42)|r1_lattices(X41,X43,X44))|X43!=k15_lattice3(X41,X42)|~m1_subset_1(X43,u1_struct_0(X41))|(v2_struct_0(X41)|~v10_lattices(X41)|~v4_lattice3(X41)|~l3_lattices(X41))|(v2_struct_0(X41)|~l3_lattices(X41))))&((m1_subset_1(esk7_3(X41,X42,X43),u1_struct_0(X41))|~r4_lattice3(X41,X43,X42)|X43=k15_lattice3(X41,X42)|~m1_subset_1(X43,u1_struct_0(X41))|(v2_struct_0(X41)|~v10_lattices(X41)|~v4_lattice3(X41)|~l3_lattices(X41))|(v2_struct_0(X41)|~l3_lattices(X41)))&((r4_lattice3(X41,esk7_3(X41,X42,X43),X42)|~r4_lattice3(X41,X43,X42)|X43=k15_lattice3(X41,X42)|~m1_subset_1(X43,u1_struct_0(X41))|(v2_struct_0(X41)|~v10_lattices(X41)|~v4_lattice3(X41)|~l3_lattices(X41))|(v2_struct_0(X41)|~l3_lattices(X41)))&(~r1_lattices(X41,X43,esk7_3(X41,X42,X43))|~r4_lattice3(X41,X43,X42)|X43=k15_lattice3(X41,X42)|~m1_subset_1(X43,u1_struct_0(X41))|(v2_struct_0(X41)|~v10_lattices(X41)|~v4_lattice3(X41)|~l3_lattices(X41))|(v2_struct_0(X41)|~l3_lattices(X41)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.19/0.53  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.53  cnf(c_0_33, plain, (r2_hidden(esk6_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.53  cnf(c_0_34, negated_conjecture, (m1_subset_1(k15_lattice3(esk12_0,X1),u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.19/0.53  cnf(c_0_35, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.53  fof(c_0_36, plain, ![X26]:((l1_lattices(X26)|~l3_lattices(X26))&(l2_lattices(X26)|~l3_lattices(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.53  cnf(c_0_37, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.53  cnf(c_0_38, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_32])).
% 0.19/0.53  cnf(c_0_39, negated_conjecture, (r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),X2)|r2_hidden(esk6_3(esk12_0,k15_lattice3(esk12_0,X1),X2),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28])]), c_0_29])).
% 0.19/0.53  fof(c_0_40, plain, ![X19]:r1_xboole_0(X19,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.53  fof(c_0_41, plain, ![X61, X62]:((k15_lattice3(X61,k6_domain_1(u1_struct_0(X61),X62))=X62|~m1_subset_1(X62,u1_struct_0(X61))|(v2_struct_0(X61)|~v10_lattices(X61)|~v4_lattice3(X61)|~l3_lattices(X61)))&(k16_lattice3(X61,k6_domain_1(u1_struct_0(X61),X62))=X62|~m1_subset_1(X62,u1_struct_0(X61))|(v2_struct_0(X61)|~v10_lattices(X61)|~v4_lattice3(X61)|~l3_lattices(X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).
% 0.19/0.53  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),u1_struct_0(esk12_0))|v13_lattices(esk12_0)|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_29])).
% 0.19/0.53  cnf(c_0_43, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.53  fof(c_0_44, plain, ![X20]:(((((((~v2_struct_0(X20)|(v2_struct_0(X20)|~v10_lattices(X20))|~l3_lattices(X20))&(v4_lattices(X20)|(v2_struct_0(X20)|~v10_lattices(X20))|~l3_lattices(X20)))&(v5_lattices(X20)|(v2_struct_0(X20)|~v10_lattices(X20))|~l3_lattices(X20)))&(v6_lattices(X20)|(v2_struct_0(X20)|~v10_lattices(X20))|~l3_lattices(X20)))&(v7_lattices(X20)|(v2_struct_0(X20)|~v10_lattices(X20))|~l3_lattices(X20)))&(v8_lattices(X20)|(v2_struct_0(X20)|~v10_lattices(X20))|~l3_lattices(X20)))&(v9_lattices(X20)|(v2_struct_0(X20)|~v10_lattices(X20))|~l3_lattices(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.53  cnf(c_0_45, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_37])).
% 0.19/0.53  cnf(c_0_46, negated_conjecture, (r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.53  cnf(c_0_47, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.53  cnf(c_0_48, plain, (k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.53  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),u1_struct_0(esk12_0))|v13_lattices(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_28])])).
% 0.19/0.53  cnf(c_0_50, negated_conjecture, (v4_lattice3(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.53  cnf(c_0_51, negated_conjecture, (v10_lattices(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.53  fof(c_0_52, plain, ![X25]:(v2_struct_0(X25)|~l1_lattices(X25)|m1_subset_1(k5_lattices(X25),u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.19/0.53  fof(c_0_53, plain, ![X27, X28, X29]:((~r1_lattices(X27,X28,X29)|k2_lattices(X27,X28,X29)=X28|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v8_lattices(X27)|~v9_lattices(X27)|~l3_lattices(X27)))&(k2_lattices(X27,X28,X29)!=X28|r1_lattices(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v8_lattices(X27)|~v9_lattices(X27)|~l3_lattices(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.19/0.53  cnf(c_0_54, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.53  cnf(c_0_55, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.53  cnf(c_0_56, plain, (r1_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_27])).
% 0.19/0.53  cnf(c_0_57, negated_conjecture, (r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.53  cnf(c_0_58, negated_conjecture, (k15_lattice3(esk12_0,k6_domain_1(u1_struct_0(esk12_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1))))=esk5_2(esk12_0,k15_lattice3(esk12_0,X1))|v13_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_28])]), c_0_29])).
% 0.19/0.53  cnf(c_0_59, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.53  cnf(c_0_60, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.53  cnf(c_0_61, negated_conjecture, (v9_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_28])]), c_0_29])).
% 0.19/0.53  cnf(c_0_62, negated_conjecture, (v8_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_51]), c_0_28])]), c_0_29])).
% 0.19/0.53  cnf(c_0_63, negated_conjecture, (r1_lattices(esk12_0,k15_lattice3(esk12_0,X1),esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))|v13_lattices(esk12_0)|~r4_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_49]), c_0_50]), c_0_51]), c_0_28])]), c_0_29])).
% 0.19/0.53  cnf(c_0_64, negated_conjecture, (r4_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),k1_xboole_0)|v13_lattices(esk12_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.53  cnf(c_0_65, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_59, c_0_43])).
% 0.19/0.53  cnf(c_0_66, negated_conjecture, (k2_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))=X1|v13_lattices(esk12_0)|~r1_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_49]), c_0_61]), c_0_62]), c_0_28])]), c_0_29])).
% 0.19/0.53  cnf(c_0_67, negated_conjecture, (r1_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1)))|v13_lattices(esk12_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.53  fof(c_0_68, plain, ![X21, X22, X23]:(((k2_lattices(X21,X22,X23)=X22|~m1_subset_1(X23,u1_struct_0(X21))|X22!=k5_lattices(X21)|~m1_subset_1(X22,u1_struct_0(X21))|~v13_lattices(X21)|(v2_struct_0(X21)|~l1_lattices(X21)))&(k2_lattices(X21,X23,X22)=X22|~m1_subset_1(X23,u1_struct_0(X21))|X22!=k5_lattices(X21)|~m1_subset_1(X22,u1_struct_0(X21))|~v13_lattices(X21)|(v2_struct_0(X21)|~l1_lattices(X21))))&((m1_subset_1(esk3_2(X21,X22),u1_struct_0(X21))|X22=k5_lattices(X21)|~m1_subset_1(X22,u1_struct_0(X21))|~v13_lattices(X21)|(v2_struct_0(X21)|~l1_lattices(X21)))&(k2_lattices(X21,X22,esk3_2(X21,X22))!=X22|k2_lattices(X21,esk3_2(X21,X22),X22)!=X22|X22=k5_lattices(X21)|~m1_subset_1(X22,u1_struct_0(X21))|~v13_lattices(X21)|(v2_struct_0(X21)|~l1_lattices(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.19/0.53  cnf(c_0_69, negated_conjecture, (m1_subset_1(k5_lattices(esk12_0),u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_28]), c_0_29])).
% 0.19/0.53  cnf(c_0_70, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk5_2(X1,X2))!=X2|k2_lattices(X1,esk5_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.53  cnf(c_0_71, negated_conjecture, (k2_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1)))=k15_lattice3(esk12_0,k1_xboole_0)|v13_lattices(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_34])])).
% 0.19/0.53  fof(c_0_72, plain, ![X46, X47, X48]:((~v6_lattices(X46)|(~m1_subset_1(X47,u1_struct_0(X46))|(~m1_subset_1(X48,u1_struct_0(X46))|k2_lattices(X46,X47,X48)=k2_lattices(X46,X48,X47)))|(v2_struct_0(X46)|~l1_lattices(X46)))&((m1_subset_1(esk8_1(X46),u1_struct_0(X46))|v6_lattices(X46)|(v2_struct_0(X46)|~l1_lattices(X46)))&((m1_subset_1(esk9_1(X46),u1_struct_0(X46))|v6_lattices(X46)|(v2_struct_0(X46)|~l1_lattices(X46)))&(k2_lattices(X46,esk8_1(X46),esk9_1(X46))!=k2_lattices(X46,esk9_1(X46),esk8_1(X46))|v6_lattices(X46)|(v2_struct_0(X46)|~l1_lattices(X46)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.19/0.53  cnf(c_0_73, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.53  cnf(c_0_74, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.53  cnf(c_0_75, negated_conjecture, (k2_lattices(esk12_0,X1,k5_lattices(esk12_0))=X1|~r1_lattices(esk12_0,X1,k5_lattices(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_69]), c_0_61]), c_0_62]), c_0_28])]), c_0_29])).
% 0.19/0.53  cnf(c_0_76, negated_conjecture, (r1_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0))|~r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_69]), c_0_50]), c_0_51]), c_0_28])]), c_0_29])).
% 0.19/0.53  cnf(c_0_77, negated_conjecture, (v13_lattices(esk12_0)|k2_lattices(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)),k15_lattice3(esk12_0,k1_xboole_0))!=k15_lattice3(esk12_0,k1_xboole_0)|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_34])]), c_0_29])).
% 0.19/0.53  cnf(c_0_78, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.53  cnf(c_0_79, negated_conjecture, (v6_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_51]), c_0_28])]), c_0_29])).
% 0.19/0.53  cnf(c_0_80, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]), c_0_59])).
% 0.19/0.53  cnf(c_0_81, negated_conjecture, (k2_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0))=k15_lattice3(esk12_0,X1)|~r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_34])])).
% 0.19/0.53  cnf(c_0_82, negated_conjecture, (v13_lattices(esk12_0)|k2_lattices(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)),k15_lattice3(esk12_0,k1_xboole_0))!=k15_lattice3(esk12_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_43]), c_0_28])])).
% 0.19/0.53  cnf(c_0_83, negated_conjecture, (k2_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2))=k2_lattices(esk12_0,k15_lattice3(esk12_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_34]), c_0_79])]), c_0_29])).
% 0.19/0.53  cnf(c_0_84, negated_conjecture, (v2_struct_0(esk12_0)|~v10_lattices(esk12_0)|~v13_lattices(esk12_0)|~l3_lattices(esk12_0)|k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.53  cnf(c_0_85, negated_conjecture, (k15_lattice3(esk12_0,X1)=k5_lattices(esk12_0)|~r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)|~v13_lattices(esk12_0)|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_34])]), c_0_29])).
% 0.19/0.53  cnf(c_0_86, negated_conjecture, (v13_lattices(esk12_0)|~l1_lattices(esk12_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_49]), c_0_71])).
% 0.19/0.53  cnf(c_0_87, negated_conjecture, (r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)|r2_hidden(esk6_3(esk12_0,k5_lattices(esk12_0),X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_69]), c_0_28])]), c_0_29])).
% 0.19/0.53  cnf(c_0_88, negated_conjecture, (k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0)|~v13_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_28]), c_0_51])]), c_0_29])).
% 0.19/0.53  cnf(c_0_89, negated_conjecture, (k15_lattice3(esk12_0,X1)=k5_lattices(esk12_0)|~r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)|~l1_lattices(esk12_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.53  cnf(c_0_90, negated_conjecture, (r4_lattice3(esk12_0,k5_lattices(esk12_0),k1_xboole_0)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_87])).
% 0.19/0.53  cnf(c_0_91, negated_conjecture, (k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0)|~l1_lattices(esk12_0)), inference(spm,[status(thm)],[c_0_88, c_0_86])).
% 0.19/0.53  cnf(c_0_92, negated_conjecture, (k15_lattice3(esk12_0,X1)=k5_lattices(esk12_0)|~r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_43]), c_0_28])])).
% 0.19/0.53  cnf(c_0_93, negated_conjecture, (r4_lattice3(esk12_0,k5_lattices(esk12_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_47])).
% 0.19/0.53  cnf(c_0_94, negated_conjecture, (k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_43]), c_0_28])])).
% 0.19/0.53  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), ['proof']).
% 0.19/0.53  # SZS output end CNFRefutation
% 0.19/0.53  # Proof object total steps             : 96
% 0.19/0.53  # Proof object clause steps            : 63
% 0.19/0.53  # Proof object formula steps           : 33
% 0.19/0.53  # Proof object conjectures             : 41
% 0.19/0.53  # Proof object clause conjectures      : 38
% 0.19/0.53  # Proof object formula conjectures     : 3
% 0.19/0.53  # Proof object initial clauses used    : 23
% 0.19/0.53  # Proof object initial formulas used   : 16
% 0.19/0.53  # Proof object generating inferences   : 36
% 0.19/0.53  # Proof object simplifying inferences  : 76
% 0.19/0.53  # Training examples: 0 positive, 0 negative
% 0.19/0.53  # Parsed axioms                        : 19
% 0.19/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.53  # Initial clauses                      : 59
% 0.19/0.53  # Removed in clause preprocessing      : 1
% 0.19/0.53  # Initial clauses in saturation        : 58
% 0.19/0.53  # Processed clauses                    : 2059
% 0.19/0.53  # ...of these trivial                  : 18
% 0.19/0.53  # ...subsumed                          : 1159
% 0.19/0.53  # ...remaining for further processing  : 882
% 0.19/0.53  # Other redundant clauses eliminated   : 6
% 0.19/0.53  # Clauses deleted for lack of memory   : 0
% 0.19/0.53  # Backward-subsumed                    : 101
% 0.19/0.53  # Backward-rewritten                   : 5
% 0.19/0.53  # Generated clauses                    : 5937
% 0.19/0.53  # ...of the previous two non-trivial   : 5238
% 0.19/0.53  # Contextual simplify-reflections      : 15
% 0.19/0.53  # Paramodulations                      : 5931
% 0.19/0.53  # Factorizations                       : 0
% 0.19/0.53  # Equation resolutions                 : 6
% 0.19/0.53  # Propositional unsat checks           : 0
% 0.19/0.53  #    Propositional check models        : 0
% 0.19/0.53  #    Propositional check unsatisfiable : 0
% 0.19/0.53  #    Propositional clauses             : 0
% 0.19/0.53  #    Propositional clauses after purity: 0
% 0.19/0.53  #    Propositional unsat core size     : 0
% 0.19/0.53  #    Propositional preprocessing time  : 0.000
% 0.19/0.53  #    Propositional encoding time       : 0.000
% 0.19/0.53  #    Propositional solver time         : 0.000
% 0.19/0.53  #    Success case prop preproc time    : 0.000
% 0.19/0.53  #    Success case prop encoding time   : 0.000
% 0.19/0.53  #    Success case prop solver time     : 0.000
% 0.19/0.53  # Current number of processed clauses  : 713
% 0.19/0.53  #    Positive orientable unit clauses  : 52
% 0.19/0.53  #    Positive unorientable unit clauses: 0
% 0.19/0.53  #    Negative unit clauses             : 4
% 0.19/0.53  #    Non-unit-clauses                  : 657
% 0.19/0.53  # Current number of unprocessed clauses: 3286
% 0.19/0.53  # ...number of literals in the above   : 11203
% 0.19/0.53  # Current number of archived formulas  : 0
% 0.19/0.53  # Current number of archived clauses   : 164
% 0.19/0.53  # Clause-clause subsumption calls (NU) : 56276
% 0.19/0.53  # Rec. Clause-clause subsumption calls : 33234
% 0.19/0.53  # Non-unit clause-clause subsumptions  : 1267
% 0.19/0.53  # Unit Clause-clause subsumption calls : 1083
% 0.19/0.53  # Rewrite failures with RHS unbound    : 0
% 0.19/0.53  # BW rewrite match attempts            : 160
% 0.19/0.53  # BW rewrite match successes           : 5
% 0.19/0.53  # Condensation attempts                : 0
% 0.19/0.53  # Condensation successes               : 0
% 0.19/0.53  # Termbank termtop insertions          : 149213
% 0.19/0.53  
% 0.19/0.53  # -------------------------------------------------
% 0.19/0.53  # User time                : 0.188 s
% 0.19/0.53  # System time              : 0.007 s
% 0.19/0.53  # Total time               : 0.195 s
% 0.19/0.53  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
