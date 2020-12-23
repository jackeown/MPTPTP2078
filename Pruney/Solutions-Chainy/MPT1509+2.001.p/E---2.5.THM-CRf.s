%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:04 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 575 expanded)
%              Number of clauses        :   69 ( 196 expanded)
%              Number of leaves         :   16 ( 140 expanded)
%              Depth                    :   12
%              Number of atoms          :  545 (3526 expanded)
%              Number of equality atoms :   72 ( 715 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t26_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattices(X1,X2,X3)
                  & r1_lattices(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(dt_l2_lattices,axiom,(
    ! [X1] :
      ( l2_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k1_lattices(X1,X2,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

fof(t42_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r3_lattice3(X1,X2,X3) )
             => k16_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(d9_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v9_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
              & k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t43_lattice3])).

fof(c_0_17,plain,(
    ! [X50,X51,X52,X53] :
      ( ( r4_lattice3(X50,X52,X51)
        | X52 != k15_lattice3(X50,X51)
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50)
        | v2_struct_0(X50)
        | ~ l3_lattices(X50) )
      & ( ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ r4_lattice3(X50,X53,X51)
        | r1_lattices(X50,X52,X53)
        | X52 != k15_lattice3(X50,X51)
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50)
        | v2_struct_0(X50)
        | ~ l3_lattices(X50) )
      & ( m1_subset_1(esk6_3(X50,X51,X52),u1_struct_0(X50))
        | ~ r4_lattice3(X50,X52,X51)
        | X52 = k15_lattice3(X50,X51)
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50)
        | v2_struct_0(X50)
        | ~ l3_lattices(X50) )
      & ( r4_lattice3(X50,esk6_3(X50,X51,X52),X51)
        | ~ r4_lattice3(X50,X52,X51)
        | X52 = k15_lattice3(X50,X51)
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50)
        | v2_struct_0(X50)
        | ~ l3_lattices(X50) )
      & ( ~ r1_lattices(X50,X52,esk6_3(X50,X51,X52))
        | ~ r4_lattice3(X50,X52,X51)
        | X52 = k15_lattice3(X50,X51)
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50)
        | v2_struct_0(X50)
        | ~ l3_lattices(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( v1_xboole_0(X13)
      | ~ m1_subset_1(X14,X13)
      | k6_domain_1(X13,X14) = k1_tarski(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v10_lattices(esk9_0)
    & v4_lattice3(esk9_0)
    & l3_lattices(esk9_0)
    & m1_subset_1(esk10_0,u1_struct_0(esk9_0))
    & ( k15_lattice3(esk9_0,k6_domain_1(u1_struct_0(esk9_0),esk10_0)) != esk10_0
      | k16_lattice3(esk9_0,k6_domain_1(u1_struct_0(esk9_0),esk10_0)) != esk10_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_20,plain,(
    ! [X15] :
      ( ( ~ v2_struct_0(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v4_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v5_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v6_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v7_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v8_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v9_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_21,plain,(
    ! [X44,X45,X46,X47,X48] :
      ( ( ~ r4_lattice3(X44,X45,X46)
        | ~ m1_subset_1(X47,u1_struct_0(X44))
        | ~ r2_hidden(X47,X46)
        | r1_lattices(X44,X47,X45)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ l3_lattices(X44) )
      & ( m1_subset_1(esk5_3(X44,X45,X48),u1_struct_0(X44))
        | r4_lattice3(X44,X45,X48)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ l3_lattices(X44) )
      & ( r2_hidden(esk5_3(X44,X45,X48),X48)
        | r4_lattice3(X44,X45,X48)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ l3_lattices(X44) )
      & ( ~ r1_lattices(X44,esk5_3(X44,X45,X48),X45)
        | r4_lattice3(X44,X45,X48)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ l3_lattices(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_22,plain,(
    ! [X60,X61] :
      ( v2_struct_0(X60)
      | ~ l3_lattices(X60)
      | m1_subset_1(k15_lattice3(X60,X61),u1_struct_0(X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_23,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v4_lattices(X31)
      | ~ l2_lattices(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | ~ r1_lattices(X31,X32,X33)
      | ~ r1_lattices(X31,X33,X32)
      | X32 = X33 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_28,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v10_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( l3_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk9_0),esk10_0) = k1_tarski(esk10_0)
    | v1_xboole_0(u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v4_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_39,plain,(
    ! [X22] :
      ( ( l1_lattices(X22)
        | ~ l3_lattices(X22) )
      & ( l2_lattices(X22)
        | ~ l3_lattices(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_lattices(esk9_0,esk10_0,X1)
    | ~ r4_lattice3(esk9_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ r2_hidden(esk10_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_30])]),c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk9_0,X1),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_31])).

cnf(c_0_42,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v4_lattice3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( k15_lattice3(esk9_0,k6_domain_1(u1_struct_0(esk9_0),esk10_0)) != esk10_0
    | k16_lattice3(esk9_0,k6_domain_1(u1_struct_0(esk9_0),esk10_0)) != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk9_0),esk10_0) = k1_tarski(esk10_0)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_31])).

fof(c_0_47,plain,(
    ! [X21] :
      ( ~ l2_lattices(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l2_lattices])])).

cnf(c_0_48,negated_conjecture,
    ( X1 = esk10_0
    | ~ r1_lattices(esk9_0,esk10_0,X1)
    | ~ r1_lattices(esk9_0,X1,esk10_0)
    | ~ l2_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_38])]),c_0_31])).

cnf(c_0_49,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattices(esk9_0,esk10_0,k15_lattice3(esk9_0,X1))
    | ~ r4_lattice3(esk9_0,k15_lattice3(esk9_0,X1),X2)
    | ~ r2_hidden(esk10_0,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r4_lattice3(esk9_0,k15_lattice3(esk9_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_52,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k15_lattice3(esk9_0,k1_tarski(esk10_0)) != esk10_0
    | k16_lattice3(esk9_0,k1_tarski(esk10_0)) != esk10_0
    | ~ l1_struct_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( l1_struct_0(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( X1 = esk10_0
    | ~ r1_lattices(esk9_0,esk10_0,X1)
    | ~ r1_lattices(esk9_0,X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_30])])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattices(esk9_0,esk10_0,k15_lattice3(esk9_0,X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_33])).

fof(c_0_58,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_59,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v6_lattices(X26)
      | ~ v8_lattices(X26)
      | ~ v9_lattices(X26)
      | ~ l3_lattices(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | k1_lattices(X26,X27,X27) = X27 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).

cnf(c_0_60,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_61,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( k15_lattice3(esk9_0,k1_tarski(esk10_0)) != esk10_0
    | k16_lattice3(esk9_0,k1_tarski(esk10_0)) != esk10_0
    | ~ l2_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( k15_lattice3(esk9_0,X1) = esk10_0
    | ~ r1_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk10_0)
    | ~ r2_hidden(esk10_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_41])])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk10_0)
    | ~ r4_lattice3(esk9_0,esk10_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_26]),c_0_43]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_67,plain,(
    ! [X62,X63,X64] :
      ( v2_struct_0(X62)
      | ~ v10_lattices(X62)
      | ~ v4_lattice3(X62)
      | ~ l3_lattices(X62)
      | ~ m1_subset_1(X63,u1_struct_0(X62))
      | ~ r2_hidden(X63,X64)
      | ~ r3_lattice3(X62,X63,X64)
      | k16_lattice3(X62,X64) = X63 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_lattice3])])])])).

cnf(c_0_68,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_70,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r1_lattices(X28,X29,X30)
        | k2_lattices(X28,X29,X30) = X29
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v8_lattices(X28)
        | ~ v9_lattices(X28)
        | ~ l3_lattices(X28) )
      & ( k2_lattices(X28,X29,X30) != X29
        | r1_lattices(X28,X29,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v8_lattices(X28)
        | ~ v9_lattices(X28)
        | ~ l3_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

fof(c_0_71,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v9_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | k2_lattices(X16,X17,k1_lattices(X16,X17,X18)) = X17
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( m1_subset_1(esk2_1(X16),u1_struct_0(X16))
        | v9_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( m1_subset_1(esk3_1(X16),u1_struct_0(X16))
        | v9_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( k2_lattices(X16,esk2_1(X16),k1_lattices(X16,esk2_1(X16),esk3_1(X16))) != esk2_1(X16)
        | v9_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | k1_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( v9_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_74,negated_conjecture,
    ( v8_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_75,negated_conjecture,
    ( v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_76,plain,(
    ! [X38,X39,X40,X41,X42] :
      ( ( ~ r3_lattice3(X38,X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ r2_hidden(X41,X40)
        | r1_lattices(X38,X39,X41)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ l3_lattices(X38) )
      & ( m1_subset_1(esk4_3(X38,X39,X42),u1_struct_0(X38))
        | r3_lattice3(X38,X39,X42)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ l3_lattices(X38) )
      & ( r2_hidden(esk4_3(X38,X39,X42),X42)
        | r3_lattice3(X38,X39,X42)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ l3_lattices(X38) )
      & ( ~ r1_lattices(X38,X39,esk4_3(X38,X39,X42))
        | r3_lattice3(X38,X39,X42)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ l3_lattices(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_77,negated_conjecture,
    ( k15_lattice3(esk9_0,k1_tarski(esk10_0)) != esk10_0
    | k16_lattice3(esk9_0,k1_tarski(esk10_0)) != esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_49]),c_0_30])])).

cnf(c_0_78,negated_conjecture,
    ( k15_lattice3(esk9_0,X1) = esk10_0
    | ~ r4_lattice3(esk9_0,esk10_0,X1)
    | ~ r2_hidden(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).

cnf(c_0_80,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_81,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( r4_lattice3(esk9_0,esk10_0,X1)
    | r2_hidden(esk5_3(esk9_0,esk10_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_26]),c_0_30])]),c_0_31])).

cnf(c_0_83,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_84,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_85,negated_conjecture,
    ( k1_lattices(esk9_0,esk10_0,esk10_0) = esk10_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_26]),c_0_73]),c_0_74]),c_0_75]),c_0_30])]),c_0_31])).

cnf(c_0_86,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( k16_lattice3(esk9_0,k1_tarski(esk10_0)) != esk10_0
    | ~ r4_lattice3(esk9_0,esk10_0,k1_tarski(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_88,negated_conjecture,
    ( k16_lattice3(esk9_0,X1) = esk10_0
    | ~ r3_lattice3(esk9_0,esk10_0,X1)
    | ~ r2_hidden(esk10_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_26]),c_0_43]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_89,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk5_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_90,negated_conjecture,
    ( esk5_3(esk9_0,esk10_0,k1_tarski(X1)) = X1
    | r4_lattice3(esk9_0,esk10_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( r1_lattices(esk9_0,X1,esk10_0)
    | k2_lattices(esk9_0,X1,esk10_0) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_26]),c_0_73]),c_0_74]),c_0_30])]),c_0_31])).

cnf(c_0_92,negated_conjecture,
    ( k2_lattices(esk9_0,esk10_0,esk10_0) = esk10_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_73]),c_0_30]),c_0_26])]),c_0_31])).

cnf(c_0_93,negated_conjecture,
    ( r3_lattice3(esk9_0,esk10_0,X1)
    | r2_hidden(esk4_3(esk9_0,esk10_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_26]),c_0_30])]),c_0_31])).

cnf(c_0_94,negated_conjecture,
    ( ~ r4_lattice3(esk9_0,esk10_0,k1_tarski(esk10_0))
    | ~ r3_lattice3(esk9_0,esk10_0,k1_tarski(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_79])])).

cnf(c_0_95,negated_conjecture,
    ( r4_lattice3(esk9_0,esk10_0,k1_tarski(X1))
    | ~ r1_lattices(esk9_0,X1,esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_30]),c_0_26])]),c_0_31])).

cnf(c_0_96,negated_conjecture,
    ( r1_lattices(esk9_0,esk10_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_26])])).

cnf(c_0_97,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk4_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_98,negated_conjecture,
    ( esk4_3(esk9_0,esk10_0,k1_tarski(X1)) = X1
    | r3_lattice3(esk9_0,esk10_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( ~ r3_lattice3(esk9_0,esk10_0,k1_tarski(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])])).

cnf(c_0_100,negated_conjecture,
    ( r3_lattice3(esk9_0,esk10_0,k1_tarski(X1))
    | ~ r1_lattices(esk9_0,esk10_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_30]),c_0_26])]),c_0_31])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.20/0.40  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.031 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t43_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattice3)).
% 0.20/0.40  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 0.20/0.40  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.40  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.40  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.20/0.40  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.20/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.40  fof(t26_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 0.20/0.40  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.20/0.40  fof(dt_l2_lattices, axiom, ![X1]:(l2_lattices(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l2_lattices)).
% 0.20/0.40  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.40  fof(t17_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k1_lattices(X1,X2,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattices)).
% 0.20/0.40  fof(t42_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 0.20/0.40  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.20/0.40  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 0.20/0.40  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.20/0.40  fof(c_0_16, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2)))), inference(assume_negation,[status(cth)],[t43_lattice3])).
% 0.20/0.40  fof(c_0_17, plain, ![X50, X51, X52, X53]:(((r4_lattice3(X50,X52,X51)|X52!=k15_lattice3(X50,X51)|~m1_subset_1(X52,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50))|(v2_struct_0(X50)|~l3_lattices(X50)))&(~m1_subset_1(X53,u1_struct_0(X50))|(~r4_lattice3(X50,X53,X51)|r1_lattices(X50,X52,X53))|X52!=k15_lattice3(X50,X51)|~m1_subset_1(X52,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50))|(v2_struct_0(X50)|~l3_lattices(X50))))&((m1_subset_1(esk6_3(X50,X51,X52),u1_struct_0(X50))|~r4_lattice3(X50,X52,X51)|X52=k15_lattice3(X50,X51)|~m1_subset_1(X52,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50))|(v2_struct_0(X50)|~l3_lattices(X50)))&((r4_lattice3(X50,esk6_3(X50,X51,X52),X51)|~r4_lattice3(X50,X52,X51)|X52=k15_lattice3(X50,X51)|~m1_subset_1(X52,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50))|(v2_struct_0(X50)|~l3_lattices(X50)))&(~r1_lattices(X50,X52,esk6_3(X50,X51,X52))|~r4_lattice3(X50,X52,X51)|X52=k15_lattice3(X50,X51)|~m1_subset_1(X52,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50))|(v2_struct_0(X50)|~l3_lattices(X50)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.20/0.40  fof(c_0_18, plain, ![X13, X14]:(v1_xboole_0(X13)|~m1_subset_1(X14,X13)|k6_domain_1(X13,X14)=k1_tarski(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.40  fof(c_0_19, negated_conjecture, ((((~v2_struct_0(esk9_0)&v10_lattices(esk9_0))&v4_lattice3(esk9_0))&l3_lattices(esk9_0))&(m1_subset_1(esk10_0,u1_struct_0(esk9_0))&(k15_lattice3(esk9_0,k6_domain_1(u1_struct_0(esk9_0),esk10_0))!=esk10_0|k16_lattice3(esk9_0,k6_domain_1(u1_struct_0(esk9_0),esk10_0))!=esk10_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.20/0.40  fof(c_0_20, plain, ![X15]:(((((((~v2_struct_0(X15)|(v2_struct_0(X15)|~v10_lattices(X15))|~l3_lattices(X15))&(v4_lattices(X15)|(v2_struct_0(X15)|~v10_lattices(X15))|~l3_lattices(X15)))&(v5_lattices(X15)|(v2_struct_0(X15)|~v10_lattices(X15))|~l3_lattices(X15)))&(v6_lattices(X15)|(v2_struct_0(X15)|~v10_lattices(X15))|~l3_lattices(X15)))&(v7_lattices(X15)|(v2_struct_0(X15)|~v10_lattices(X15))|~l3_lattices(X15)))&(v8_lattices(X15)|(v2_struct_0(X15)|~v10_lattices(X15))|~l3_lattices(X15)))&(v9_lattices(X15)|(v2_struct_0(X15)|~v10_lattices(X15))|~l3_lattices(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.40  fof(c_0_21, plain, ![X44, X45, X46, X47, X48]:((~r4_lattice3(X44,X45,X46)|(~m1_subset_1(X47,u1_struct_0(X44))|(~r2_hidden(X47,X46)|r1_lattices(X44,X47,X45)))|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~l3_lattices(X44)))&((m1_subset_1(esk5_3(X44,X45,X48),u1_struct_0(X44))|r4_lattice3(X44,X45,X48)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~l3_lattices(X44)))&((r2_hidden(esk5_3(X44,X45,X48),X48)|r4_lattice3(X44,X45,X48)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~l3_lattices(X44)))&(~r1_lattices(X44,esk5_3(X44,X45,X48),X45)|r4_lattice3(X44,X45,X48)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~l3_lattices(X44)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.20/0.40  fof(c_0_22, plain, ![X60, X61]:(v2_struct_0(X60)|~l3_lattices(X60)|m1_subset_1(k15_lattice3(X60,X61),u1_struct_0(X60))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.20/0.40  cnf(c_0_23, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_24, plain, ![X12]:(v2_struct_0(X12)|~l1_struct_0(X12)|~v1_xboole_0(u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.40  cnf(c_0_25, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  fof(c_0_27, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~v4_lattices(X31)|~l2_lattices(X31)|(~m1_subset_1(X32,u1_struct_0(X31))|(~m1_subset_1(X33,u1_struct_0(X31))|(~r1_lattices(X31,X32,X33)|~r1_lattices(X31,X33,X32)|X32=X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).
% 0.20/0.40  cnf(c_0_28, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (v10_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (l3_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_32, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_33, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_34, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_35, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (k6_domain_1(u1_struct_0(esk9_0),esk10_0)=k1_tarski(esk10_0)|v1_xboole_0(u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.40  cnf(c_0_37, plain, (v2_struct_0(X1)|X2=X3|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)|~r1_lattices(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (v4_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])]), c_0_31])).
% 0.20/0.40  fof(c_0_39, plain, ![X22]:((l1_lattices(X22)|~l3_lattices(X22))&(l2_lattices(X22)|~l3_lattices(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (r1_lattices(esk9_0,esk10_0,X1)|~r4_lattice3(esk9_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~r2_hidden(esk10_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (m1_subset_1(k15_lattice3(esk9_0,X1),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_30]), c_0_31])).
% 0.20/0.40  cnf(c_0_42, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_33])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (v4_lattice3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_44, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (k15_lattice3(esk9_0,k6_domain_1(u1_struct_0(esk9_0),esk10_0))!=esk10_0|k16_lattice3(esk9_0,k6_domain_1(u1_struct_0(esk9_0),esk10_0))!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (k6_domain_1(u1_struct_0(esk9_0),esk10_0)=k1_tarski(esk10_0)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_31])).
% 0.20/0.40  fof(c_0_47, plain, ![X21]:(~l2_lattices(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l2_lattices])])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (X1=esk10_0|~r1_lattices(esk9_0,esk10_0,X1)|~r1_lattices(esk9_0,X1,esk10_0)|~l2_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_38])]), c_0_31])).
% 0.20/0.40  cnf(c_0_49, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (r1_lattices(esk9_0,esk10_0,k15_lattice3(esk9_0,X1))|~r4_lattice3(esk9_0,k15_lattice3(esk9_0,X1),X2)|~r2_hidden(esk10_0,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (r4_lattice3(esk9_0,k15_lattice3(esk9_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_29]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_52, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_44])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (k15_lattice3(esk9_0,k1_tarski(esk10_0))!=esk10_0|k16_lattice3(esk9_0,k1_tarski(esk10_0))!=esk10_0|~l1_struct_0(esk9_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.40  cnf(c_0_54, plain, (l1_struct_0(X1)|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (X1=esk10_0|~r1_lattices(esk9_0,esk10_0,X1)|~r1_lattices(esk9_0,X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_30])])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (r1_lattices(esk9_0,esk10_0,k15_lattice3(esk9_0,X1))|~r2_hidden(esk10_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.40  cnf(c_0_57, plain, (r1_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_33])).
% 0.20/0.40  fof(c_0_58, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.40  fof(c_0_59, plain, ![X26, X27]:(v2_struct_0(X26)|~v6_lattices(X26)|~v8_lattices(X26)|~v9_lattices(X26)|~l3_lattices(X26)|(~m1_subset_1(X27,u1_struct_0(X26))|k1_lattices(X26,X27,X27)=X27)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).
% 0.20/0.40  cnf(c_0_60, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_61, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_62, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (k15_lattice3(esk9_0,k1_tarski(esk10_0))!=esk10_0|k16_lattice3(esk9_0,k1_tarski(esk10_0))!=esk10_0|~l2_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (k15_lattice3(esk9_0,X1)=esk10_0|~r1_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk10_0)|~r2_hidden(esk10_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_41])])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk10_0)|~r4_lattice3(esk9_0,esk10_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_26]), c_0_43]), c_0_29]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_66, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.40  fof(c_0_67, plain, ![X62, X63, X64]:(v2_struct_0(X62)|~v10_lattices(X62)|~v4_lattice3(X62)|~l3_lattices(X62)|(~m1_subset_1(X63,u1_struct_0(X62))|(~r2_hidden(X63,X64)|~r3_lattice3(X62,X63,X64)|k16_lattice3(X62,X64)=X63))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_lattice3])])])])).
% 0.20/0.40  cnf(c_0_68, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.40  cnf(c_0_69, plain, (r2_hidden(esk5_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  fof(c_0_70, plain, ![X28, X29, X30]:((~r1_lattices(X28,X29,X30)|k2_lattices(X28,X29,X30)=X29|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v8_lattices(X28)|~v9_lattices(X28)|~l3_lattices(X28)))&(k2_lattices(X28,X29,X30)!=X29|r1_lattices(X28,X29,X30)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v8_lattices(X28)|~v9_lattices(X28)|~l3_lattices(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.20/0.40  fof(c_0_71, plain, ![X16, X17, X18]:((~v9_lattices(X16)|(~m1_subset_1(X17,u1_struct_0(X16))|(~m1_subset_1(X18,u1_struct_0(X16))|k2_lattices(X16,X17,k1_lattices(X16,X17,X18))=X17))|(v2_struct_0(X16)|~l3_lattices(X16)))&((m1_subset_1(esk2_1(X16),u1_struct_0(X16))|v9_lattices(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))&((m1_subset_1(esk3_1(X16),u1_struct_0(X16))|v9_lattices(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))&(k2_lattices(X16,esk2_1(X16),k1_lattices(X16,esk2_1(X16),esk3_1(X16)))!=esk2_1(X16)|v9_lattices(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.20/0.40  cnf(c_0_72, plain, (v2_struct_0(X1)|k1_lattices(X1,X2,X2)=X2|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (v9_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_29]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (v8_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_29]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_29]), c_0_30])]), c_0_31])).
% 0.20/0.40  fof(c_0_76, plain, ![X38, X39, X40, X41, X42]:((~r3_lattice3(X38,X39,X40)|(~m1_subset_1(X41,u1_struct_0(X38))|(~r2_hidden(X41,X40)|r1_lattices(X38,X39,X41)))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~l3_lattices(X38)))&((m1_subset_1(esk4_3(X38,X39,X42),u1_struct_0(X38))|r3_lattice3(X38,X39,X42)|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~l3_lattices(X38)))&((r2_hidden(esk4_3(X38,X39,X42),X42)|r3_lattice3(X38,X39,X42)|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~l3_lattices(X38)))&(~r1_lattices(X38,X39,esk4_3(X38,X39,X42))|r3_lattice3(X38,X39,X42)|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~l3_lattices(X38)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (k15_lattice3(esk9_0,k1_tarski(esk10_0))!=esk10_0|k16_lattice3(esk9_0,k1_tarski(esk10_0))!=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_49]), c_0_30])])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (k15_lattice3(esk9_0,X1)=esk10_0|~r4_lattice3(esk9_0,esk10_0,X1)|~r2_hidden(esk10_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.40  cnf(c_0_79, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).
% 0.20/0.40  cnf(c_0_80, plain, (v2_struct_0(X1)|k16_lattice3(X1,X3)=X2|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X2,X3)|~r3_lattice3(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.40  cnf(c_0_81, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_68])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (r4_lattice3(esk9_0,esk10_0,X1)|r2_hidden(esk5_3(esk9_0,esk10_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_26]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_83, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.40  cnf(c_0_84, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.40  cnf(c_0_85, negated_conjecture, (k1_lattices(esk9_0,esk10_0,esk10_0)=esk10_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_26]), c_0_73]), c_0_74]), c_0_75]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_86, plain, (r2_hidden(esk4_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.40  cnf(c_0_87, negated_conjecture, (k16_lattice3(esk9_0,k1_tarski(esk10_0))!=esk10_0|~r4_lattice3(esk9_0,esk10_0,k1_tarski(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.20/0.40  cnf(c_0_88, negated_conjecture, (k16_lattice3(esk9_0,X1)=esk10_0|~r3_lattice3(esk9_0,esk10_0,X1)|~r2_hidden(esk10_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_26]), c_0_43]), c_0_29]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_89, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk5_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_90, negated_conjecture, (esk5_3(esk9_0,esk10_0,k1_tarski(X1))=X1|r4_lattice3(esk9_0,esk10_0,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.40  cnf(c_0_91, negated_conjecture, (r1_lattices(esk9_0,X1,esk10_0)|k2_lattices(esk9_0,X1,esk10_0)!=X1|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_26]), c_0_73]), c_0_74]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_92, negated_conjecture, (k2_lattices(esk9_0,esk10_0,esk10_0)=esk10_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_73]), c_0_30]), c_0_26])]), c_0_31])).
% 0.20/0.40  cnf(c_0_93, negated_conjecture, (r3_lattice3(esk9_0,esk10_0,X1)|r2_hidden(esk4_3(esk9_0,esk10_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_26]), c_0_30])]), c_0_31])).
% 0.20/0.40  cnf(c_0_94, negated_conjecture, (~r4_lattice3(esk9_0,esk10_0,k1_tarski(esk10_0))|~r3_lattice3(esk9_0,esk10_0,k1_tarski(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_79])])).
% 0.20/0.40  cnf(c_0_95, negated_conjecture, (r4_lattice3(esk9_0,esk10_0,k1_tarski(X1))|~r1_lattices(esk9_0,X1,esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_30]), c_0_26])]), c_0_31])).
% 0.20/0.40  cnf(c_0_96, negated_conjecture, (r1_lattices(esk9_0,esk10_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_26])])).
% 0.20/0.40  cnf(c_0_97, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk4_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.40  cnf(c_0_98, negated_conjecture, (esk4_3(esk9_0,esk10_0,k1_tarski(X1))=X1|r3_lattice3(esk9_0,esk10_0,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_81, c_0_93])).
% 0.20/0.40  cnf(c_0_99, negated_conjecture, (~r3_lattice3(esk9_0,esk10_0,k1_tarski(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])])).
% 0.20/0.40  cnf(c_0_100, negated_conjecture, (r3_lattice3(esk9_0,esk10_0,k1_tarski(X1))|~r1_lattices(esk9_0,esk10_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_30]), c_0_26])]), c_0_31])).
% 0.20/0.40  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_96])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 102
% 0.20/0.40  # Proof object clause steps            : 69
% 0.20/0.40  # Proof object formula steps           : 33
% 0.20/0.40  # Proof object conjectures             : 43
% 0.20/0.40  # Proof object clause conjectures      : 40
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 29
% 0.20/0.40  # Proof object initial formulas used   : 16
% 0.20/0.40  # Proof object generating inferences   : 34
% 0.20/0.40  # Proof object simplifying inferences  : 89
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 19
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 51
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 50
% 0.20/0.40  # Processed clauses                    : 220
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 19
% 0.20/0.40  # ...remaining for further processing  : 201
% 0.20/0.40  # Other redundant clauses eliminated   : 6
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 8
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 321
% 0.20/0.40  # ...of the previous two non-trivial   : 256
% 0.20/0.40  # Contextual simplify-reflections      : 2
% 0.20/0.40  # Paramodulations                      : 316
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 6
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 139
% 0.20/0.40  #    Positive orientable unit clauses  : 20
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 2
% 0.20/0.40  #    Non-unit-clauses                  : 117
% 0.20/0.40  # Current number of unprocessed clauses: 136
% 0.20/0.40  # ...number of literals in the above   : 530
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 58
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 3781
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 871
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 26
% 0.20/0.40  # Unit Clause-clause subsumption calls : 92
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 11
% 0.20/0.40  # BW rewrite match successes           : 1
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 14464
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.051 s
% 0.20/0.40  # System time              : 0.002 s
% 0.20/0.40  # Total time               : 0.054 s
% 0.20/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
