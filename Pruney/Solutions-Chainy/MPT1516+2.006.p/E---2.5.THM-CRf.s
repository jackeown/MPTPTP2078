%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:06 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   78 (1197 expanded)
%              Number of clauses        :   51 ( 411 expanded)
%              Number of leaves         :   13 ( 302 expanded)
%              Depth                    :   26
%              Number of atoms          :  474 (8056 expanded)
%              Number of equality atoms :   46 ( 730 expanded)
%              Maximal formula depth    :   14 (   6 average)
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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X18,X19,X20] :
      ( ( k2_lattices(X18,X19,X20) = X19
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | X19 != k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X20,X19) = X19
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | X19 != k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( m1_subset_1(esk2_2(X18,X19),u1_struct_0(X18))
        | X19 = k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X19,esk2_2(X18,X19)) != X19
        | k2_lattices(X18,esk2_2(X18,X19),X19) != X19
        | X19 = k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_15,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_lattices(X22)
      | m1_subset_1(k5_lattices(X22),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_16,plain,(
    ! [X23] :
      ( ( l1_lattices(X23)
        | ~ l3_lattices(X23) )
      & ( l2_lattices(X23)
        | ~ l3_lattices(X23) ) ) ),
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_18,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
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

cnf(c_0_21,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X40,X41] :
      ( v2_struct_0(X40)
      | ~ l3_lattices(X40)
      | m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_23,negated_conjecture,
    ( v2_struct_0(esk9_0)
    | ~ v10_lattices(esk9_0)
    | ~ v13_lattices(esk9_0)
    | ~ l3_lattices(esk9_0)
    | k5_lattices(esk9_0) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( l3_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v10_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19])).

cnf(c_0_28,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k5_lattices(esk9_0) != k15_lattice3(esk9_0,k1_xboole_0)
    | ~ v13_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_32,plain,
    ( X1 = k5_lattices(X2)
    | v2_struct_0(X2)
    | ~ r1_lattices(X2,X1,k5_lattices(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v13_lattices(X2)
    | ~ v9_lattices(X2)
    | ~ v8_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk9_0,X1),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_26])).

fof(c_0_34,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r3_lattices(X24,X25,X26)
        | r1_lattices(X24,X25,X26)
        | v2_struct_0(X24)
        | ~ v6_lattices(X24)
        | ~ v8_lattices(X24)
        | ~ v9_lattices(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24)) )
      & ( ~ r1_lattices(X24,X25,X26)
        | r3_lattices(X24,X25,X26)
        | v2_struct_0(X24)
        | ~ v6_lattices(X24)
        | ~ v8_lattices(X24)
        | ~ v9_lattices(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_35,plain,(
    ! [X52,X53,X54] :
      ( ( r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))
        | ~ r1_tarski(X53,X54)
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) )
      & ( r3_lattices(X52,k16_lattice3(X52,X54),k16_lattice3(X52,X53))
        | ~ r1_tarski(X53,X54)
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).

fof(c_0_36,plain,(
    ! [X50,X51] :
      ( ( k15_lattice3(X50,k6_domain_1(u1_struct_0(X50),X51)) = X51
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) )
      & ( k16_lattice3(X50,k6_domain_1(u1_struct_0(X50),X51)) = X51
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))
    | ~ v13_lattices(esk9_0)
    | ~ v9_lattices(esk9_0)
    | ~ v8_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_24])]),c_0_26])]),c_0_33])])).

cnf(c_0_38,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk9_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_26])).

cnf(c_0_40,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_tarski(X2,X3)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_43,negated_conjecture,
    ( ~ r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))
    | ~ v13_lattices(esk9_0)
    | ~ v9_lattices(esk9_0)
    | ~ v8_lattices(esk9_0)
    | ~ v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_33]),c_0_24])]),c_0_26])).

cnf(c_0_44,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_tarski(X2,k6_domain_1(u1_struct_0(X1),X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( v4_lattice3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_47,plain,(
    ! [X30,X32,X33] :
      ( ( m1_subset_1(esk3_1(X30),u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,esk3_1(X30),X32) = esk3_1(X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,X32,esk3_1(X30)) = esk3_1(X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( m1_subset_1(esk4_2(X30,X33),u1_struct_0(X30))
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,X33,esk4_2(X30,X33)) != X33
        | k2_lattices(X30,esk4_2(X30,X33),X33) != X33
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v13_lattices(esk9_0)
    | ~ v9_lattices(esk9_0)
    | ~ v8_lattices(esk9_0)
    | ~ v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_39]),c_0_25]),c_0_24]),c_0_46])]),c_0_26])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l1_lattices(esk9_0)
    | ~ v9_lattices(esk9_0)
    | ~ v8_lattices(esk9_0)
    | ~ v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_26])).

fof(c_0_51,plain,(
    ! [X17] :
      ( ( ~ v2_struct_0(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v4_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v5_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v6_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v7_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v8_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v9_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v9_lattices(esk9_0)
    | ~ v8_lattices(esk9_0)
    | ~ v6_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_21]),c_0_24])])).

cnf(c_0_53,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v8_lattices(esk9_0)
    | ~ v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_55,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk4_2(X1,X2)) != X2
    | k2_lattices(X1,esk4_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_58,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,esk4_2(X1,X2),X2) != X2
    | ~ r1_lattices(X1,X2,esk4_2(X1,X2))
    | ~ m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_28]),c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( v13_lattices(esk9_0)
    | k2_lattices(esk9_0,esk4_2(esk9_0,X1),X1) != X1
    | ~ r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v9_lattices(esk9_0)
    | ~ v8_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_24])]),c_0_26])).

fof(c_0_62,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v6_lattices(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | k2_lattices(X35,X36,X37) = k2_lattices(X35,X37,X36)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk5_1(X35),u1_struct_0(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk6_1(X35),u1_struct_0(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,esk5_1(X35),esk6_1(X35)) != k2_lattices(X35,esk6_1(X35),esk5_1(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_63,negated_conjecture,
    ( v13_lattices(esk9_0)
    | k2_lattices(esk9_0,esk4_2(esk9_0,X1),X1) != X1
    | ~ r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v8_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_53]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_64,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( v13_lattices(esk9_0)
    | k2_lattices(esk9_0,esk4_2(esk9_0,X1),X1) != X1
    | ~ r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_55]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_66,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_28]),c_0_21])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v9_lattices(esk9_0)
    | ~ v8_lattices(esk9_0)
    | ~ v6_lattices(esk9_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_24])]),c_0_26]),c_0_60]),c_0_48])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v8_lattices(esk9_0)
    | ~ v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_53]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_55]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_58]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_71,negated_conjecture,
    ( ~ r3_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v9_lattices(esk9_0)
    | ~ v8_lattices(esk9_0)
    | ~ v6_lattices(esk9_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_38]),c_0_24])]),c_0_26]),c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( ~ r3_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v8_lattices(esk9_0)
    | ~ v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_53]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( ~ r3_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_55]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_74,negated_conjecture,
    ( ~ r3_lattices(esk9_0,X1,esk4_2(esk9_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_58]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_75,negated_conjecture,
    ( ~ m1_subset_1(esk4_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))
    | ~ r1_tarski(X1,k6_domain_1(u1_struct_0(esk9_0),esk4_2(esk9_0,k15_lattice3(esk9_0,X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_44]),c_0_33]),c_0_45]),c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_subset_1(esk4_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_46])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_60]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:29:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 2.06/2.25  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 2.06/2.25  # and selection function PSelectUnlessUniqMaxPos.
% 2.06/2.25  #
% 2.06/2.25  # Preprocessing time       : 0.030 s
% 2.06/2.25  # Presaturation interreduction done
% 2.06/2.25  
% 2.06/2.25  # Proof found!
% 2.06/2.25  # SZS status Theorem
% 2.06/2.25  # SZS output start CNFRefutation
% 2.06/2.25  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 2.06/2.25  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 2.06/2.25  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.06/2.25  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.06/2.25  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 2.06/2.25  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 2.06/2.25  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.06/2.25  fof(t46_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 2.06/2.25  fof(t43_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattice3)).
% 2.06/2.25  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.06/2.25  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 2.06/2.25  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.06/2.25  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 2.06/2.25  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 2.06/2.25  fof(c_0_14, plain, ![X18, X19, X20]:(((k2_lattices(X18,X19,X20)=X19|~m1_subset_1(X20,u1_struct_0(X18))|X19!=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X20,X19)=X19|~m1_subset_1(X20,u1_struct_0(X18))|X19!=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18))))&((m1_subset_1(esk2_2(X18,X19),u1_struct_0(X18))|X19=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X19,esk2_2(X18,X19))!=X19|k2_lattices(X18,esk2_2(X18,X19),X19)!=X19|X19=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 2.06/2.25  fof(c_0_15, plain, ![X22]:(v2_struct_0(X22)|~l1_lattices(X22)|m1_subset_1(k5_lattices(X22),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 2.06/2.25  fof(c_0_16, plain, ![X23]:((l1_lattices(X23)|~l3_lattices(X23))&(l2_lattices(X23)|~l3_lattices(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 2.06/2.25  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk9_0)&v10_lattices(esk9_0))&v4_lattice3(esk9_0))&l3_lattices(esk9_0))&(v2_struct_0(esk9_0)|~v10_lattices(esk9_0)|~v13_lattices(esk9_0)|~l3_lattices(esk9_0)|k5_lattices(esk9_0)!=k15_lattice3(esk9_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 2.06/2.25  cnf(c_0_18, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.06/2.25  cnf(c_0_19, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.06/2.25  fof(c_0_20, plain, ![X27, X28, X29]:((~r1_lattices(X27,X28,X29)|k2_lattices(X27,X28,X29)=X28|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v8_lattices(X27)|~v9_lattices(X27)|~l3_lattices(X27)))&(k2_lattices(X27,X28,X29)!=X28|r1_lattices(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v8_lattices(X27)|~v9_lattices(X27)|~l3_lattices(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 2.06/2.25  cnf(c_0_21, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.06/2.25  fof(c_0_22, plain, ![X40, X41]:(v2_struct_0(X40)|~l3_lattices(X40)|m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 2.06/2.25  cnf(c_0_23, negated_conjecture, (v2_struct_0(esk9_0)|~v10_lattices(esk9_0)|~v13_lattices(esk9_0)|~l3_lattices(esk9_0)|k5_lattices(esk9_0)!=k15_lattice3(esk9_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.06/2.25  cnf(c_0_24, negated_conjecture, (l3_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.06/2.25  cnf(c_0_25, negated_conjecture, (v10_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.06/2.25  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.06/2.25  cnf(c_0_27, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]), c_0_19])).
% 2.06/2.25  cnf(c_0_28, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.06/2.25  cnf(c_0_29, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 2.06/2.25  cnf(c_0_30, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.06/2.25  cnf(c_0_31, negated_conjecture, (k5_lattices(esk9_0)!=k15_lattice3(esk9_0,k1_xboole_0)|~v13_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), c_0_26])).
% 2.06/2.25  cnf(c_0_32, plain, (X1=k5_lattices(X2)|v2_struct_0(X2)|~r1_lattices(X2,X1,k5_lattices(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v13_lattices(X2)|~v9_lattices(X2)|~v8_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_21]), c_0_29])).
% 2.06/2.25  cnf(c_0_33, negated_conjecture, (m1_subset_1(k15_lattice3(esk9_0,X1),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_26])).
% 2.06/2.25  fof(c_0_34, plain, ![X24, X25, X26]:((~r3_lattices(X24,X25,X26)|r1_lattices(X24,X25,X26)|(v2_struct_0(X24)|~v6_lattices(X24)|~v8_lattices(X24)|~v9_lattices(X24)|~l3_lattices(X24)|~m1_subset_1(X25,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))))&(~r1_lattices(X24,X25,X26)|r3_lattices(X24,X25,X26)|(v2_struct_0(X24)|~v6_lattices(X24)|~v8_lattices(X24)|~v9_lattices(X24)|~l3_lattices(X24)|~m1_subset_1(X25,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 2.06/2.25  fof(c_0_35, plain, ![X52, X53, X54]:((r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))|~r1_tarski(X53,X54)|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))&(r3_lattices(X52,k16_lattice3(X52,X54),k16_lattice3(X52,X53))|~r1_tarski(X53,X54)|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).
% 2.06/2.25  fof(c_0_36, plain, ![X50, X51]:((k15_lattice3(X50,k6_domain_1(u1_struct_0(X50),X51))=X51|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))&(k16_lattice3(X50,k6_domain_1(u1_struct_0(X50),X51))=X51|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).
% 2.06/2.25  cnf(c_0_37, negated_conjecture, (~r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))|~v13_lattices(esk9_0)|~v9_lattices(esk9_0)|~v8_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_24])]), c_0_26])]), c_0_33])])).
% 2.06/2.25  cnf(c_0_38, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.06/2.25  cnf(c_0_39, negated_conjecture, (m1_subset_1(k5_lattices(esk9_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_26])).
% 2.06/2.25  cnf(c_0_40, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~r1_tarski(X2,X3)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.06/2.25  cnf(c_0_41, plain, (k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.06/2.25  fof(c_0_42, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 2.06/2.25  cnf(c_0_43, negated_conjecture, (~r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))|~v13_lattices(esk9_0)|~v9_lattices(esk9_0)|~v8_lattices(esk9_0)|~v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_33]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_44, plain, (r3_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r1_tarski(X2,k6_domain_1(u1_struct_0(X1),X3))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 2.06/2.25  cnf(c_0_45, negated_conjecture, (v4_lattice3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.06/2.25  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.06/2.25  fof(c_0_47, plain, ![X30, X32, X33]:(((m1_subset_1(esk3_1(X30),u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&((k2_lattices(X30,esk3_1(X30),X32)=esk3_1(X30)|~m1_subset_1(X32,u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,X32,esk3_1(X30))=esk3_1(X30)|~m1_subset_1(X32,u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))))&((m1_subset_1(esk4_2(X30,X33),u1_struct_0(X30))|~m1_subset_1(X33,u1_struct_0(X30))|v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,X33,esk4_2(X30,X33))!=X33|k2_lattices(X30,esk4_2(X30,X33),X33)!=X33|~m1_subset_1(X33,u1_struct_0(X30))|v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 2.06/2.25  cnf(c_0_48, negated_conjecture, (~v13_lattices(esk9_0)|~v9_lattices(esk9_0)|~v8_lattices(esk9_0)|~v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_39]), c_0_25]), c_0_24]), c_0_46])]), c_0_26])).
% 2.06/2.25  cnf(c_0_49, plain, (m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.06/2.25  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l1_lattices(esk9_0)|~v9_lattices(esk9_0)|~v8_lattices(esk9_0)|~v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_26])).
% 2.06/2.25  fof(c_0_51, plain, ![X17]:(((((((~v2_struct_0(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17))&(v4_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v5_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v6_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v7_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v8_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v9_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 2.06/2.25  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v9_lattices(esk9_0)|~v8_lattices(esk9_0)|~v6_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_21]), c_0_24])])).
% 2.06/2.25  cnf(c_0_53, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 2.06/2.25  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v8_lattices(esk9_0)|~v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_55, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 2.06/2.25  cnf(c_0_56, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk4_2(X1,X2))!=X2|k2_lattices(X1,esk4_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.06/2.25  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_58, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 2.06/2.25  cnf(c_0_59, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,esk4_2(X1,X2),X2)!=X2|~r1_lattices(X1,X2,esk4_2(X1,X2))|~m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_28]), c_0_21])).
% 2.06/2.25  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk4_2(esk9_0,X1),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_61, negated_conjecture, (v13_lattices(esk9_0)|k2_lattices(esk9_0,esk4_2(esk9_0,X1),X1)!=X1|~r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v9_lattices(esk9_0)|~v8_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_24])]), c_0_26])).
% 2.06/2.25  fof(c_0_62, plain, ![X35, X36, X37]:((~v6_lattices(X35)|(~m1_subset_1(X36,u1_struct_0(X35))|(~m1_subset_1(X37,u1_struct_0(X35))|k2_lattices(X35,X36,X37)=k2_lattices(X35,X37,X36)))|(v2_struct_0(X35)|~l1_lattices(X35)))&((m1_subset_1(esk5_1(X35),u1_struct_0(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&((m1_subset_1(esk6_1(X35),u1_struct_0(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&(k2_lattices(X35,esk5_1(X35),esk6_1(X35))!=k2_lattices(X35,esk6_1(X35),esk5_1(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 2.06/2.25  cnf(c_0_63, negated_conjecture, (v13_lattices(esk9_0)|k2_lattices(esk9_0,esk4_2(esk9_0,X1),X1)!=X1|~r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v8_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_53]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_64, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 2.06/2.25  cnf(c_0_65, negated_conjecture, (v13_lattices(esk9_0)|k2_lattices(esk9_0,esk4_2(esk9_0,X1),X1)!=X1|~r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_55]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_66, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X3,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_28]), c_0_21])).
% 2.06/2.25  cnf(c_0_67, negated_conjecture, (~r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v9_lattices(esk9_0)|~v8_lattices(esk9_0)|~v6_lattices(esk9_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_24])]), c_0_26]), c_0_60]), c_0_48])).
% 2.06/2.25  cnf(c_0_68, negated_conjecture, (~r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v8_lattices(esk9_0)|~v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_53]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_69, negated_conjecture, (~r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_55]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_70, negated_conjecture, (~r1_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_58]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_71, negated_conjecture, (~r3_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v9_lattices(esk9_0)|~v8_lattices(esk9_0)|~v6_lattices(esk9_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_38]), c_0_24])]), c_0_26]), c_0_60])).
% 2.06/2.25  cnf(c_0_72, negated_conjecture, (~r3_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v8_lattices(esk9_0)|~v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_53]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_73, negated_conjecture, (~r3_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_55]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_74, negated_conjecture, (~r3_lattices(esk9_0,X1,esk4_2(esk9_0,X1))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_58]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_75, negated_conjecture, (~m1_subset_1(esk4_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))|~r1_tarski(X1,k6_domain_1(u1_struct_0(esk9_0),esk4_2(esk9_0,k15_lattice3(esk9_0,X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_44]), c_0_33]), c_0_45]), c_0_25]), c_0_24])]), c_0_26])).
% 2.06/2.25  cnf(c_0_76, negated_conjecture, (~m1_subset_1(esk4_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_75, c_0_46])).
% 2.06/2.25  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_60]), c_0_33])]), ['proof']).
% 2.06/2.25  # SZS output end CNFRefutation
% 2.06/2.25  # Proof object total steps             : 78
% 2.06/2.25  # Proof object clause steps            : 51
% 2.06/2.25  # Proof object formula steps           : 27
% 2.06/2.25  # Proof object conjectures             : 33
% 2.06/2.25  # Proof object clause conjectures      : 30
% 2.06/2.25  # Proof object formula conjectures     : 3
% 2.06/2.25  # Proof object initial clauses used    : 20
% 2.06/2.25  # Proof object initial formulas used   : 13
% 2.06/2.25  # Proof object generating inferences   : 29
% 2.06/2.25  # Proof object simplifying inferences  : 97
% 2.06/2.25  # Training examples: 0 positive, 0 negative
% 2.06/2.25  # Parsed axioms                        : 18
% 2.06/2.25  # Removed by relevancy pruning/SinE    : 0
% 2.06/2.25  # Initial clauses                      : 53
% 2.06/2.25  # Removed in clause preprocessing      : 1
% 2.06/2.25  # Initial clauses in saturation        : 52
% 2.06/2.25  # Processed clauses                    : 10499
% 2.06/2.25  # ...of these trivial                  : 0
% 2.06/2.25  # ...subsumed                          : 7217
% 2.06/2.25  # ...remaining for further processing  : 3282
% 2.06/2.25  # Other redundant clauses eliminated   : 151
% 2.06/2.25  # Clauses deleted for lack of memory   : 0
% 2.06/2.25  # Backward-subsumed                    : 85
% 2.06/2.25  # Backward-rewritten                   : 0
% 2.06/2.25  # Generated clauses                    : 112478
% 2.06/2.25  # ...of the previous two non-trivial   : 109403
% 2.06/2.25  # Contextual simplify-reflections      : 223
% 2.06/2.25  # Paramodulations                      : 112303
% 2.06/2.25  # Factorizations                       : 24
% 2.06/2.25  # Equation resolutions                 : 151
% 2.06/2.25  # Propositional unsat checks           : 0
% 2.06/2.25  #    Propositional check models        : 0
% 2.06/2.25  #    Propositional check unsatisfiable : 0
% 2.06/2.25  #    Propositional clauses             : 0
% 2.06/2.25  #    Propositional clauses after purity: 0
% 2.06/2.25  #    Propositional unsat core size     : 0
% 2.06/2.25  #    Propositional preprocessing time  : 0.000
% 2.06/2.25  #    Propositional encoding time       : 0.000
% 2.06/2.25  #    Propositional solver time         : 0.000
% 2.06/2.25  #    Success case prop preproc time    : 0.000
% 2.06/2.25  #    Success case prop encoding time   : 0.000
% 2.06/2.25  #    Success case prop solver time     : 0.000
% 2.06/2.25  # Current number of processed clauses  : 3141
% 2.06/2.25  #    Positive orientable unit clauses  : 7
% 2.06/2.25  #    Positive unorientable unit clauses: 0
% 2.06/2.25  #    Negative unit clauses             : 2
% 2.06/2.25  #    Non-unit-clauses                  : 3132
% 2.06/2.25  # Current number of unprocessed clauses: 98785
% 2.06/2.25  # ...number of literals in the above   : 1044182
% 2.06/2.25  # Current number of archived formulas  : 0
% 2.06/2.25  # Current number of archived clauses   : 136
% 2.06/2.25  # Clause-clause subsumption calls (NU) : 5290051
% 2.06/2.25  # Rec. Clause-clause subsumption calls : 320054
% 2.06/2.25  # Non-unit clause-clause subsumptions  : 7421
% 2.06/2.25  # Unit Clause-clause subsumption calls : 276
% 2.06/2.25  # Rewrite failures with RHS unbound    : 0
% 2.06/2.25  # BW rewrite match attempts            : 3
% 2.06/2.25  # BW rewrite match successes           : 0
% 2.06/2.25  # Condensation attempts                : 0
% 2.06/2.25  # Condensation successes               : 0
% 2.06/2.25  # Termbank termtop insertions          : 2983529
% 2.06/2.26  
% 2.06/2.26  # -------------------------------------------------
% 2.06/2.26  # User time                : 1.861 s
% 2.06/2.26  # System time              : 0.067 s
% 2.06/2.26  # Total time               : 1.928 s
% 2.06/2.26  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
