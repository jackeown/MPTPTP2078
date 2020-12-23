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
% DateTime   : Thu Dec  3 11:10:23 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  141 (3535 expanded)
%              Number of clauses        :  114 (1184 expanded)
%              Number of leaves         :   13 ( 864 expanded)
%              Depth                    :   17
%              Number of atoms          :  521 (26191 expanded)
%              Number of equality atoms :  120 (6101 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v11_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( k4_lattices(X1,X2,X3) = k4_lattices(X1,X2,X4)
                      & k3_lattices(X1,X2,X3) = k3_lattices(X1,X2,X4) )
                   => X3 = X4 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).

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

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

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

fof(d3_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k1_lattices(X1,X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(d8_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v8_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(d11_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v11_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => k2_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k2_lattices(X1,X2,X3),k2_lattices(X1,X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v11_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( k4_lattices(X1,X2,X3) = k4_lattices(X1,X2,X4)
                        & k3_lattices(X1,X2,X3) = k3_lattices(X1,X2,X4) )
                     => X3 = X4 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_lattices])).

fof(c_0_14,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v4_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v5_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v6_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v8_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v9_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v10_lattices(esk9_0)
    & v11_lattices(esk9_0)
    & l3_lattices(esk9_0)
    & m1_subset_1(esk10_0,u1_struct_0(esk9_0))
    & m1_subset_1(esk11_0,u1_struct_0(esk9_0))
    & m1_subset_1(esk12_0,u1_struct_0(esk9_0))
    & k4_lattices(esk9_0,esk10_0,esk11_0) = k4_lattices(esk9_0,esk10_0,esk12_0)
    & k3_lattices(esk9_0,esk10_0,esk11_0) = k3_lattices(esk9_0,esk10_0,esk12_0)
    & esk11_0 != esk12_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X41,X42,X43] :
      ( v2_struct_0(X41)
      | ~ v6_lattices(X41)
      | ~ l1_lattices(X41)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | ~ m1_subset_1(X43,u1_struct_0(X41))
      | k4_lattices(X41,X42,X43) = k2_lattices(X41,X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_17,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v10_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l3_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ v6_lattices(X34)
      | ~ l1_lattices(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | m1_subset_1(k4_lattices(X34,X35,X36),u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk12_0,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_25,plain,(
    ! [X37] :
      ( ( l1_lattices(X37)
        | ~ l3_lattices(X37) )
      & ( l2_lattices(X37)
        | ~ l3_lattices(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_26,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v6_lattices(X9)
      | ~ l1_lattices(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | k4_lattices(X9,X10,X11) = k4_lattices(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk12_0) = k2_lattices(esk9_0,X1,esk12_0)
    | ~ l1_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_20])).

cnf(c_0_29,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk11_0,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk9_0,X1,esk12_0),u1_struct_0(esk9_0))
    | ~ l1_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_24])]),c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk12_0) = k2_lattices(esk9_0,X1,esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])])).

fof(c_0_34,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r1_lattices(X46,X47,X48)
        | k2_lattices(X46,X47,X48) = X47
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v8_lattices(X46)
        | ~ v9_lattices(X46)
        | ~ l3_lattices(X46) )
      & ( k2_lattices(X46,X47,X48) != X47
        | r1_lattices(X46,X47,X48)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v8_lattices(X46)
        | ~ v9_lattices(X46)
        | ~ l3_lattices(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_35,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_37,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_lattices(X19,X20,X21)
        | k1_lattices(X19,X20,X21) = X21
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ l2_lattices(X19) )
      & ( k1_lattices(X19,X20,X21) != X21
        | r1_lattices(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ l2_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_38,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk12_0) = k4_lattices(esk9_0,esk12_0,X1)
    | ~ l1_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_24])]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk11_0) = k2_lattices(esk9_0,X1,esk11_0)
    | ~ l1_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_31]),c_0_24])]),c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk11_0) = k4_lattices(esk9_0,esk11_0,X1)
    | ~ l1_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24])]),c_0_20])).

fof(c_0_41,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ v4_lattices(X38)
      | ~ l2_lattices(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | k3_lattices(X38,X39,X40) = k1_lattices(X38,X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_42,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_43,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ v4_lattices(X6)
      | ~ l2_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k3_lattices(X6,X7,X8) = k3_lattices(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk9_0,X1,esk12_0),u1_struct_0(esk9_0))
    | ~ l1_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( v9_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( v8_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_48,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk12_0) = k4_lattices(esk9_0,esk12_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_19])])).

cnf(c_0_50,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk11_0) = k2_lattices(esk9_0,X1,esk11_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_29]),c_0_19])])).

cnf(c_0_51,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk11_0) = k4_lattices(esk9_0,esk11_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_29]),c_0_19])])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( v4_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk9_0,X1,esk12_0),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_19])])).

cnf(c_0_56,negated_conjecture,
    ( k2_lattices(esk9_0,X1,esk12_0) = X1
    | ~ r1_lattices(esk9_0,X1,esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23]),c_0_46]),c_0_47]),c_0_19])]),c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattices(esk9_0,X1,esk12_0)
    | k1_lattices(esk9_0,X1,esk12_0) != esk12_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_23]),c_0_20])).

cnf(c_0_58,negated_conjecture,
    ( k4_lattices(esk9_0,esk10_0,esk11_0) = k4_lattices(esk9_0,esk10_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( k4_lattices(esk9_0,esk12_0,esk12_0) = k2_lattices(esk9_0,esk12_0,esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_49]),c_0_23])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk9_0,X1,esk11_0),u1_struct_0(esk9_0))
    | ~ l1_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_31]),c_0_24])]),c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( k4_lattices(esk9_0,esk11_0,esk11_0) = k2_lattices(esk9_0,esk11_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_31])])).

cnf(c_0_63,negated_conjecture,
    ( k3_lattices(esk9_0,X1,esk11_0) = k1_lattices(esk9_0,X1,esk11_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_31]),c_0_53])]),c_0_20])).

cnf(c_0_64,negated_conjecture,
    ( k3_lattices(esk9_0,X1,esk11_0) = k3_lattices(esk9_0,esk11_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_31]),c_0_53])]),c_0_20])).

cnf(c_0_65,negated_conjecture,
    ( k3_lattices(esk9_0,X1,k2_lattices(esk9_0,X2,esk12_0)) = k1_lattices(esk9_0,X1,k2_lattices(esk9_0,X2,esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_55]),c_0_53])]),c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( k2_lattices(esk9_0,X1,esk12_0) = X1
    | k1_lattices(esk9_0,X1,esk12_0) != esk12_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_67,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v8_lattices(X29)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | k1_lattices(X29,k2_lattices(X29,X30,X31),X31) = X31
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( m1_subset_1(esk7_1(X29),u1_struct_0(X29))
        | v8_lattices(X29)
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( m1_subset_1(esk8_1(X29),u1_struct_0(X29))
        | v8_lattices(X29)
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( k1_lattices(X29,k2_lattices(X29,esk7_1(X29),esk8_1(X29)),esk8_1(X29)) != esk8_1(X29)
        | v8_lattices(X29)
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk9_0,esk10_0,esk11_0),u1_struct_0(esk9_0))
    | ~ l1_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_58]),c_0_59])])).

cnf(c_0_69,negated_conjecture,
    ( k4_lattices(esk9_0,esk10_0,esk11_0) = k2_lattices(esk9_0,esk10_0,esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_33]),c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk9_0,esk12_0,esk12_0),u1_struct_0(esk9_0))
    | ~ l1_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_60]),c_0_23])])).

fof(c_0_71,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v11_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | k2_lattices(X12,X13,k1_lattices(X12,X14,X15)) = k1_lattices(X12,k2_lattices(X12,X13,X14),k2_lattices(X12,X13,X15))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk1_1(X12),u1_struct_0(X12))
        | v11_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk2_1(X12),u1_struct_0(X12))
        | v11_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk3_1(X12),u1_struct_0(X12))
        | v11_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( k2_lattices(X12,esk1_1(X12),k1_lattices(X12,esk2_1(X12),esk3_1(X12))) != k1_lattices(X12,k2_lattices(X12,esk1_1(X12),esk2_1(X12)),k2_lattices(X12,esk1_1(X12),esk3_1(X12)))
        | v11_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_lattices])])])])])])).

cnf(c_0_72,negated_conjecture,
    ( k3_lattices(esk9_0,X1,esk12_0) = k1_lattices(esk9_0,X1,esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_23]),c_0_53])]),c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( k3_lattices(esk9_0,X1,esk12_0) = k3_lattices(esk9_0,esk12_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_23]),c_0_53])]),c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( k3_lattices(esk9_0,esk10_0,esk11_0) = k3_lattices(esk9_0,esk10_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk9_0,esk11_0,esk11_0),u1_struct_0(esk9_0))
    | ~ l1_lattices(esk9_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_51]),c_0_31])]),c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( k3_lattices(esk9_0,esk11_0,X1) = k1_lattices(esk9_0,X1,esk11_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( k3_lattices(esk9_0,X1,X2) = k1_lattices(esk9_0,X1,X2)
    | k1_lattices(esk9_0,X2,esk12_0) != esk12_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_78,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk9_0,esk10_0,esk12_0),u1_struct_0(esk9_0))
    | ~ l1_lattices(esk9_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk9_0,esk12_0,esk12_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_29]),c_0_19])])).

cnf(c_0_81,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k2_lattices(X1,X2,X3),k2_lattices(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ v11_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( v11_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_83,plain,(
    ! [X44,X45] :
      ( v2_struct_0(X44)
      | ~ v6_lattices(X44)
      | ~ v8_lattices(X44)
      | ~ v9_lattices(X44)
      | ~ l3_lattices(X44)
      | ~ m1_subset_1(X45,u1_struct_0(X44))
      | k1_lattices(X44,X45,X45) = X45 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).

cnf(c_0_84,negated_conjecture,
    ( k3_lattices(esk9_0,esk12_0,X1) = k1_lattices(esk9_0,X1,esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_85,negated_conjecture,
    ( k3_lattices(esk9_0,X1,esk10_0) = k1_lattices(esk9_0,X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_59]),c_0_53])]),c_0_20])).

cnf(c_0_86,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk10_0) = k2_lattices(esk9_0,X1,esk10_0)
    | ~ l1_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_59]),c_0_24])]),c_0_20])).

cnf(c_0_87,negated_conjecture,
    ( k3_lattices(esk9_0,esk10_0,esk11_0) = k1_lattices(esk9_0,esk10_0,esk12_0)
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_72]),c_0_59])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk9_0,esk11_0,esk11_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_29]),c_0_19])])).

cnf(c_0_89,negated_conjecture,
    ( k1_lattices(esk9_0,esk11_0,X1) = k1_lattices(esk9_0,X1,esk11_0)
    | k1_lattices(esk9_0,X1,esk12_0) != esk12_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_31])])).

cnf(c_0_90,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_91,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,X1,esk12_0),esk12_0) = esk12_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_23]),c_0_47]),c_0_19])]),c_0_20])).

cnf(c_0_92,negated_conjecture,
    ( k2_lattices(esk9_0,esk10_0,esk12_0) = k2_lattices(esk9_0,esk10_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_50]),c_0_59])])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk9_0,esk10_0,esk12_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_29]),c_0_19])])).

cnf(c_0_94,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,X1,k2_lattices(esk9_0,esk12_0,esk12_0)),k2_lattices(esk9_0,esk12_0,esk12_0)) = k2_lattices(esk9_0,esk12_0,esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_80]),c_0_47]),c_0_19])]),c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,X1,X2),k2_lattices(esk9_0,X1,esk12_0)) = k2_lattices(esk9_0,X1,k1_lattices(esk9_0,X2,esk12_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_23]),c_0_82]),c_0_19])]),c_0_20])).

cnf(c_0_96,plain,
    ( v2_struct_0(X1)
    | k1_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_97,negated_conjecture,
    ( k4_lattices(esk9_0,esk10_0,esk12_0) = k2_lattices(esk9_0,esk10_0,esk12_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_69])).

cnf(c_0_98,negated_conjecture,
    ( k1_lattices(esk9_0,esk12_0,X1) = k1_lattices(esk9_0,X1,esk12_0)
    | k1_lattices(esk9_0,X1,esk12_0) != esk12_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_77]),c_0_23])])).

cnf(c_0_99,negated_conjecture,
    ( k3_lattices(esk9_0,esk10_0,esk11_0) = k1_lattices(esk9_0,esk12_0,esk10_0)
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_73]),c_0_74]),c_0_23]),c_0_59])])).

cnf(c_0_100,negated_conjecture,
    ( k4_lattices(esk9_0,X1,esk10_0) = k2_lattices(esk9_0,X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_29]),c_0_19])])).

cnf(c_0_101,negated_conjecture,
    ( k1_lattices(esk9_0,esk10_0,esk12_0) = k1_lattices(esk9_0,esk10_0,esk11_0)
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_63]),c_0_59])])).

cnf(c_0_102,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,X1,X2),k2_lattices(esk9_0,X1,esk11_0)) = k2_lattices(esk9_0,X1,k1_lattices(esk9_0,X2,esk11_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_31]),c_0_82]),c_0_19])]),c_0_20])).

cnf(c_0_103,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,X1,k2_lattices(esk9_0,esk11_0,esk11_0)),k2_lattices(esk9_0,esk11_0,esk11_0)) = k2_lattices(esk9_0,esk11_0,esk11_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_88]),c_0_47]),c_0_19])]),c_0_20])).

cnf(c_0_104,negated_conjecture,
    ( k2_lattices(esk9_0,X1,esk11_0) = X1
    | ~ r1_lattices(esk9_0,X1,esk11_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_31]),c_0_46]),c_0_47]),c_0_19])]),c_0_20])).

cnf(c_0_105,negated_conjecture,
    ( r1_lattices(esk9_0,X1,esk11_0)
    | k1_lattices(esk9_0,X1,esk11_0) != esk11_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_31]),c_0_20])).

cnf(c_0_106,negated_conjecture,
    ( k1_lattices(esk9_0,esk11_0,X1) = k1_lattices(esk9_0,X1,esk11_0)
    | k1_lattices(esk9_0,X1,esk12_0) != esk12_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_19])])).

cnf(c_0_107,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,esk10_0,esk11_0),esk12_0) = esk12_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_59])])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk9_0,esk10_0,esk11_0),u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_93,c_0_92])).

cnf(c_0_109,negated_conjecture,
    ( k3_lattices(esk9_0,esk10_0,esk11_0) = k1_lattices(esk9_0,esk11_0,esk10_0)
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_64]),c_0_31]),c_0_59])])).

cnf(c_0_110,negated_conjecture,
    ( k2_lattices(esk9_0,esk12_0,k1_lattices(esk9_0,k2_lattices(esk9_0,esk12_0,esk12_0),esk12_0)) = k2_lattices(esk9_0,esk12_0,esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_23]),c_0_80])])).

cnf(c_0_111,negated_conjecture,
    ( k1_lattices(esk9_0,esk12_0,esk12_0) = esk12_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_23]),c_0_46]),c_0_47]),c_0_24]),c_0_19])]),c_0_20])).

cnf(c_0_112,negated_conjecture,
    ( k4_lattices(esk9_0,esk10_0,esk12_0) = k2_lattices(esk9_0,esk10_0,esk11_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_92])).

cnf(c_0_113,negated_conjecture,
    ( k1_lattices(esk9_0,esk12_0,X1) = k1_lattices(esk9_0,X1,esk12_0)
    | k1_lattices(esk9_0,X1,esk12_0) != esk12_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_90]),c_0_19])])).

cnf(c_0_114,negated_conjecture,
    ( k1_lattices(esk9_0,esk12_0,esk10_0) = k1_lattices(esk9_0,esk10_0,esk11_0)
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_99]),c_0_59])])).

cnf(c_0_115,negated_conjecture,
    ( k4_lattices(esk9_0,esk11_0,esk12_0) = k2_lattices(esk9_0,esk12_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_23]),c_0_31])])).

cnf(c_0_116,negated_conjecture,
    ( k2_lattices(esk9_0,esk11_0,esk10_0) = k2_lattices(esk9_0,esk10_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_51]),c_0_69]),c_0_92]),c_0_31]),c_0_59])])).

cnf(c_0_117,negated_conjecture,
    ( k1_lattices(esk9_0,esk10_0,esk12_0) = k1_lattices(esk9_0,esk10_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_90]),c_0_19])])).

cnf(c_0_118,negated_conjecture,
    ( k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,k2_lattices(esk9_0,esk11_0,esk11_0),esk11_0)) = k2_lattices(esk9_0,esk11_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_88]),c_0_31])])).

cnf(c_0_119,negated_conjecture,
    ( k2_lattices(esk9_0,X1,esk11_0) = X1
    | k1_lattices(esk9_0,X1,esk11_0) != esk11_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ l2_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_120,negated_conjecture,
    ( k1_lattices(esk9_0,esk11_0,esk11_0) = esk11_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_31]),c_0_46]),c_0_47]),c_0_24]),c_0_19])]),c_0_20])).

cnf(c_0_121,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,X1,esk11_0),esk11_0) = esk11_0
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_31]),c_0_47]),c_0_19])]),c_0_20])).

cnf(c_0_122,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,esk10_0,esk11_0),esk11_0) = k1_lattices(esk9_0,esk11_0,k2_lattices(esk9_0,esk10_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108])])).

cnf(c_0_123,negated_conjecture,
    ( k1_lattices(esk9_0,esk11_0,esk10_0) = k1_lattices(esk9_0,esk10_0,esk11_0)
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_109]),c_0_59])])).

cnf(c_0_124,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,X1,X2),k2_lattices(esk9_0,X1,esk10_0)) = k2_lattices(esk9_0,X1,k1_lattices(esk9_0,X2,esk10_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_59]),c_0_82]),c_0_19])]),c_0_20])).

cnf(c_0_125,negated_conjecture,
    ( k2_lattices(esk9_0,esk12_0,esk12_0) = esk12_0
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_66]),c_0_111]),c_0_111]),c_0_23])])).

cnf(c_0_126,negated_conjecture,
    ( k2_lattices(esk9_0,esk12_0,esk10_0) = k2_lattices(esk9_0,esk10_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_49]),c_0_112]),c_0_23]),c_0_59])])).

cnf(c_0_127,negated_conjecture,
    ( k1_lattices(esk9_0,esk12_0,k2_lattices(esk9_0,esk10_0,esk11_0)) = esk12_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_107]),c_0_108])])).

cnf(c_0_128,negated_conjecture,
    ( k1_lattices(esk9_0,esk12_0,esk10_0) = k1_lattices(esk9_0,esk10_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_90]),c_0_19])])).

cnf(c_0_129,negated_conjecture,
    ( k2_lattices(esk9_0,esk12_0,esk11_0) = k2_lattices(esk9_0,esk11_0,esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_115]),c_0_31])])).

cnf(c_0_130,negated_conjecture,
    ( k1_lattices(esk9_0,k2_lattices(esk9_0,esk10_0,esk11_0),k2_lattices(esk9_0,esk11_0,esk12_0)) = k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,esk10_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_116]),c_0_117]),c_0_59]),c_0_31])])).

cnf(c_0_131,negated_conjecture,
    ( k2_lattices(esk9_0,esk11_0,esk11_0) = esk11_0
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120]),c_0_120]),c_0_31])])).

cnf(c_0_132,negated_conjecture,
    ( k1_lattices(esk9_0,esk11_0,k2_lattices(esk9_0,esk10_0,esk11_0)) = esk11_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_59])])).

cnf(c_0_133,negated_conjecture,
    ( k1_lattices(esk9_0,esk11_0,esk10_0) = k1_lattices(esk9_0,esk10_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_90]),c_0_19])])).

cnf(c_0_134,negated_conjecture,
    ( k2_lattices(esk9_0,esk12_0,k1_lattices(esk9_0,esk10_0,esk11_0)) = esk12_0
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126]),c_0_127]),c_0_128]),c_0_23])])).

cnf(c_0_135,negated_conjecture,
    ( k2_lattices(esk9_0,esk12_0,k1_lattices(esk9_0,esk10_0,esk11_0)) = k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,esk10_0,esk11_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_126]),c_0_129]),c_0_59]),c_0_23])]),c_0_130])).

cnf(c_0_136,negated_conjecture,
    ( k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,esk10_0,esk11_0)) = esk11_0
    | ~ l2_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_131]),c_0_116]),c_0_132]),c_0_133]),c_0_31])])).

cnf(c_0_137,negated_conjecture,
    ( k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,esk10_0,esk11_0)) = esk12_0
    | ~ l2_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_138,negated_conjecture,
    ( esk11_0 != esk12_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_139,negated_conjecture,
    ( ~ l2_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_138])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_90]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.37/1.53  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.37/1.53  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.37/1.53  #
% 1.37/1.53  # Preprocessing time       : 0.030 s
% 1.37/1.53  # Presaturation interreduction done
% 1.37/1.53  
% 1.37/1.53  # Proof found!
% 1.37/1.53  # SZS status Theorem
% 1.37/1.53  # SZS output start CNFRefutation
% 1.37/1.53  fof(t32_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_lattices)).
% 1.37/1.53  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 1.37/1.53  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 1.37/1.53  fof(dt_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattices)).
% 1.37/1.53  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 1.37/1.53  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 1.37/1.53  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 1.37/1.53  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 1.37/1.53  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 1.37/1.53  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 1.37/1.53  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 1.37/1.53  fof(d11_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v11_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X3,X4))=k1_lattices(X1,k2_lattices(X1,X2,X3),k2_lattices(X1,X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_lattices)).
% 1.37/1.53  fof(t17_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k1_lattices(X1,X2,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattices)).
% 1.37/1.53  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4)))))), inference(assume_negation,[status(cth)],[t32_lattices])).
% 1.37/1.53  fof(c_0_14, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 1.37/1.53  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk9_0)&v10_lattices(esk9_0))&v11_lattices(esk9_0))&l3_lattices(esk9_0))&(m1_subset_1(esk10_0,u1_struct_0(esk9_0))&(m1_subset_1(esk11_0,u1_struct_0(esk9_0))&(m1_subset_1(esk12_0,u1_struct_0(esk9_0))&((k4_lattices(esk9_0,esk10_0,esk11_0)=k4_lattices(esk9_0,esk10_0,esk12_0)&k3_lattices(esk9_0,esk10_0,esk11_0)=k3_lattices(esk9_0,esk10_0,esk12_0))&esk11_0!=esk12_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 1.37/1.53  fof(c_0_16, plain, ![X41, X42, X43]:(v2_struct_0(X41)|~v6_lattices(X41)|~l1_lattices(X41)|~m1_subset_1(X42,u1_struct_0(X41))|~m1_subset_1(X43,u1_struct_0(X41))|k4_lattices(X41,X42,X43)=k2_lattices(X41,X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 1.37/1.53  cnf(c_0_17, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.37/1.53  cnf(c_0_18, negated_conjecture, (v10_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.53  cnf(c_0_19, negated_conjecture, (l3_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.53  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.53  fof(c_0_21, plain, ![X34, X35, X36]:(v2_struct_0(X34)|~v6_lattices(X34)|~l1_lattices(X34)|~m1_subset_1(X35,u1_struct_0(X34))|~m1_subset_1(X36,u1_struct_0(X34))|m1_subset_1(k4_lattices(X34,X35,X36),u1_struct_0(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).
% 1.37/1.53  cnf(c_0_22, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.37/1.53  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk12_0,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.53  cnf(c_0_24, negated_conjecture, (v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20])).
% 1.37/1.53  fof(c_0_25, plain, ![X37]:((l1_lattices(X37)|~l3_lattices(X37))&(l2_lattices(X37)|~l3_lattices(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 1.37/1.53  fof(c_0_26, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~v6_lattices(X9)|~l1_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|k4_lattices(X9,X10,X11)=k4_lattices(X9,X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 1.37/1.53  cnf(c_0_27, plain, (v2_struct_0(X1)|m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.37/1.53  cnf(c_0_28, negated_conjecture, (k4_lattices(esk9_0,X1,esk12_0)=k2_lattices(esk9_0,X1,esk12_0)|~l1_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), c_0_20])).
% 1.37/1.53  cnf(c_0_29, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.37/1.53  cnf(c_0_30, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.37/1.53  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk11_0,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.53  cnf(c_0_32, negated_conjecture, (m1_subset_1(k4_lattices(esk9_0,X1,esk12_0),u1_struct_0(esk9_0))|~l1_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_23]), c_0_24])]), c_0_20])).
% 1.37/1.53  cnf(c_0_33, negated_conjecture, (k4_lattices(esk9_0,X1,esk12_0)=k2_lattices(esk9_0,X1,esk12_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19])])).
% 1.37/1.53  fof(c_0_34, plain, ![X46, X47, X48]:((~r1_lattices(X46,X47,X48)|k2_lattices(X46,X47,X48)=X47|~m1_subset_1(X48,u1_struct_0(X46))|~m1_subset_1(X47,u1_struct_0(X46))|(v2_struct_0(X46)|~v8_lattices(X46)|~v9_lattices(X46)|~l3_lattices(X46)))&(k2_lattices(X46,X47,X48)!=X47|r1_lattices(X46,X47,X48)|~m1_subset_1(X48,u1_struct_0(X46))|~m1_subset_1(X47,u1_struct_0(X46))|(v2_struct_0(X46)|~v8_lattices(X46)|~v9_lattices(X46)|~l3_lattices(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 1.37/1.53  cnf(c_0_35, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.37/1.53  cnf(c_0_36, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.37/1.53  fof(c_0_37, plain, ![X19, X20, X21]:((~r1_lattices(X19,X20,X21)|k1_lattices(X19,X20,X21)=X21|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l2_lattices(X19)))&(k1_lattices(X19,X20,X21)!=X21|r1_lattices(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~l2_lattices(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 1.37/1.53  cnf(c_0_38, negated_conjecture, (k4_lattices(esk9_0,X1,esk12_0)=k4_lattices(esk9_0,esk12_0,X1)|~l1_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_23]), c_0_24])]), c_0_20])).
% 1.37/1.53  cnf(c_0_39, negated_conjecture, (k4_lattices(esk9_0,X1,esk11_0)=k2_lattices(esk9_0,X1,esk11_0)|~l1_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_31]), c_0_24])]), c_0_20])).
% 1.37/1.53  cnf(c_0_40, negated_conjecture, (k4_lattices(esk9_0,X1,esk11_0)=k4_lattices(esk9_0,esk11_0,X1)|~l1_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_24])]), c_0_20])).
% 1.37/1.53  fof(c_0_41, plain, ![X38, X39, X40]:(v2_struct_0(X38)|~v4_lattices(X38)|~l2_lattices(X38)|~m1_subset_1(X39,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X38))|k3_lattices(X38,X39,X40)=k1_lattices(X38,X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 1.37/1.53  cnf(c_0_42, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.37/1.53  fof(c_0_43, plain, ![X6, X7, X8]:(v2_struct_0(X6)|~v4_lattices(X6)|~l2_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))|k3_lattices(X6,X7,X8)=k3_lattices(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 1.37/1.53  cnf(c_0_44, negated_conjecture, (m1_subset_1(k2_lattices(esk9_0,X1,esk12_0),u1_struct_0(esk9_0))|~l1_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.37/1.53  cnf(c_0_45, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.37/1.53  cnf(c_0_46, negated_conjecture, (v9_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_18]), c_0_19])]), c_0_20])).
% 1.37/1.53  cnf(c_0_47, negated_conjecture, (v8_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_18]), c_0_19])]), c_0_20])).
% 1.37/1.53  cnf(c_0_48, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.37/1.53  cnf(c_0_49, negated_conjecture, (k4_lattices(esk9_0,X1,esk12_0)=k4_lattices(esk9_0,esk12_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_29]), c_0_19])])).
% 1.37/1.53  cnf(c_0_50, negated_conjecture, (k4_lattices(esk9_0,X1,esk11_0)=k2_lattices(esk9_0,X1,esk11_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_29]), c_0_19])])).
% 1.37/1.53  cnf(c_0_51, negated_conjecture, (k4_lattices(esk9_0,X1,esk11_0)=k4_lattices(esk9_0,esk11_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_29]), c_0_19])])).
% 1.37/1.53  cnf(c_0_52, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.37/1.53  cnf(c_0_53, negated_conjecture, (v4_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_18]), c_0_19])]), c_0_20])).
% 1.37/1.53  cnf(c_0_54, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.37/1.53  cnf(c_0_55, negated_conjecture, (m1_subset_1(k2_lattices(esk9_0,X1,esk12_0),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_19])])).
% 1.37/1.53  cnf(c_0_56, negated_conjecture, (k2_lattices(esk9_0,X1,esk12_0)=X1|~r1_lattices(esk9_0,X1,esk12_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_23]), c_0_46]), c_0_47]), c_0_19])]), c_0_20])).
% 1.37/1.53  cnf(c_0_57, negated_conjecture, (r1_lattices(esk9_0,X1,esk12_0)|k1_lattices(esk9_0,X1,esk12_0)!=esk12_0|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_23]), c_0_20])).
% 1.37/1.53  cnf(c_0_58, negated_conjecture, (k4_lattices(esk9_0,esk10_0,esk11_0)=k4_lattices(esk9_0,esk10_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.53  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.53  cnf(c_0_60, negated_conjecture, (k4_lattices(esk9_0,esk12_0,esk12_0)=k2_lattices(esk9_0,esk12_0,esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_49]), c_0_23])])).
% 1.37/1.53  cnf(c_0_61, negated_conjecture, (m1_subset_1(k4_lattices(esk9_0,X1,esk11_0),u1_struct_0(esk9_0))|~l1_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_31]), c_0_24])]), c_0_20])).
% 1.37/1.53  cnf(c_0_62, negated_conjecture, (k4_lattices(esk9_0,esk11_0,esk11_0)=k2_lattices(esk9_0,esk11_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_31])])).
% 1.37/1.53  cnf(c_0_63, negated_conjecture, (k3_lattices(esk9_0,X1,esk11_0)=k1_lattices(esk9_0,X1,esk11_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_31]), c_0_53])]), c_0_20])).
% 1.37/1.53  cnf(c_0_64, negated_conjecture, (k3_lattices(esk9_0,X1,esk11_0)=k3_lattices(esk9_0,esk11_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_31]), c_0_53])]), c_0_20])).
% 1.37/1.53  cnf(c_0_65, negated_conjecture, (k3_lattices(esk9_0,X1,k2_lattices(esk9_0,X2,esk12_0))=k1_lattices(esk9_0,X1,k2_lattices(esk9_0,X2,esk12_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))|~m1_subset_1(X2,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_55]), c_0_53])]), c_0_20])).
% 1.37/1.54  cnf(c_0_66, negated_conjecture, (k2_lattices(esk9_0,X1,esk12_0)=X1|k1_lattices(esk9_0,X1,esk12_0)!=esk12_0|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.37/1.54  fof(c_0_67, plain, ![X29, X30, X31]:((~v8_lattices(X29)|(~m1_subset_1(X30,u1_struct_0(X29))|(~m1_subset_1(X31,u1_struct_0(X29))|k1_lattices(X29,k2_lattices(X29,X30,X31),X31)=X31))|(v2_struct_0(X29)|~l3_lattices(X29)))&((m1_subset_1(esk7_1(X29),u1_struct_0(X29))|v8_lattices(X29)|(v2_struct_0(X29)|~l3_lattices(X29)))&((m1_subset_1(esk8_1(X29),u1_struct_0(X29))|v8_lattices(X29)|(v2_struct_0(X29)|~l3_lattices(X29)))&(k1_lattices(X29,k2_lattices(X29,esk7_1(X29),esk8_1(X29)),esk8_1(X29))!=esk8_1(X29)|v8_lattices(X29)|(v2_struct_0(X29)|~l3_lattices(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 1.37/1.54  cnf(c_0_68, negated_conjecture, (m1_subset_1(k4_lattices(esk9_0,esk10_0,esk11_0),u1_struct_0(esk9_0))|~l1_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_58]), c_0_59])])).
% 1.37/1.54  cnf(c_0_69, negated_conjecture, (k4_lattices(esk9_0,esk10_0,esk11_0)=k2_lattices(esk9_0,esk10_0,esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_33]), c_0_59])])).
% 1.37/1.54  cnf(c_0_70, negated_conjecture, (m1_subset_1(k2_lattices(esk9_0,esk12_0,esk12_0),u1_struct_0(esk9_0))|~l1_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_60]), c_0_23])])).
% 1.37/1.54  fof(c_0_71, plain, ![X12, X13, X14, X15]:((~v11_lattices(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|(~m1_subset_1(X15,u1_struct_0(X12))|k2_lattices(X12,X13,k1_lattices(X12,X14,X15))=k1_lattices(X12,k2_lattices(X12,X13,X14),k2_lattices(X12,X13,X15)))))|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk1_1(X12),u1_struct_0(X12))|v11_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk2_1(X12),u1_struct_0(X12))|v11_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk3_1(X12),u1_struct_0(X12))|v11_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&(k2_lattices(X12,esk1_1(X12),k1_lattices(X12,esk2_1(X12),esk3_1(X12)))!=k1_lattices(X12,k2_lattices(X12,esk1_1(X12),esk2_1(X12)),k2_lattices(X12,esk1_1(X12),esk3_1(X12)))|v11_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_lattices])])])])])])).
% 1.37/1.54  cnf(c_0_72, negated_conjecture, (k3_lattices(esk9_0,X1,esk12_0)=k1_lattices(esk9_0,X1,esk12_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_23]), c_0_53])]), c_0_20])).
% 1.37/1.54  cnf(c_0_73, negated_conjecture, (k3_lattices(esk9_0,X1,esk12_0)=k3_lattices(esk9_0,esk12_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_23]), c_0_53])]), c_0_20])).
% 1.37/1.54  cnf(c_0_74, negated_conjecture, (k3_lattices(esk9_0,esk10_0,esk11_0)=k3_lattices(esk9_0,esk10_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.54  cnf(c_0_75, negated_conjecture, (m1_subset_1(k2_lattices(esk9_0,esk11_0,esk11_0),u1_struct_0(esk9_0))|~l1_lattices(esk9_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_51]), c_0_31])]), c_0_62])).
% 1.37/1.54  cnf(c_0_76, negated_conjecture, (k3_lattices(esk9_0,esk11_0,X1)=k1_lattices(esk9_0,X1,esk11_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 1.37/1.54  cnf(c_0_77, negated_conjecture, (k3_lattices(esk9_0,X1,X2)=k1_lattices(esk9_0,X1,X2)|k1_lattices(esk9_0,X2,esk12_0)!=esk12_0|~m1_subset_1(X1,u1_struct_0(esk9_0))|~m1_subset_1(X2,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.37/1.54  cnf(c_0_78, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.37/1.54  cnf(c_0_79, negated_conjecture, (m1_subset_1(k2_lattices(esk9_0,esk10_0,esk12_0),u1_struct_0(esk9_0))|~l1_lattices(esk9_0)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 1.37/1.54  cnf(c_0_80, negated_conjecture, (m1_subset_1(k2_lattices(esk9_0,esk12_0,esk12_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_29]), c_0_19])])).
% 1.37/1.54  cnf(c_0_81, plain, (k2_lattices(X1,X2,k1_lattices(X1,X3,X4))=k1_lattices(X1,k2_lattices(X1,X2,X3),k2_lattices(X1,X2,X4))|v2_struct_0(X1)|~v11_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.37/1.54  cnf(c_0_82, negated_conjecture, (v11_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.54  fof(c_0_83, plain, ![X44, X45]:(v2_struct_0(X44)|~v6_lattices(X44)|~v8_lattices(X44)|~v9_lattices(X44)|~l3_lattices(X44)|(~m1_subset_1(X45,u1_struct_0(X44))|k1_lattices(X44,X45,X45)=X45)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).
% 1.37/1.54  cnf(c_0_84, negated_conjecture, (k3_lattices(esk9_0,esk12_0,X1)=k1_lattices(esk9_0,X1,esk12_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.37/1.54  cnf(c_0_85, negated_conjecture, (k3_lattices(esk9_0,X1,esk10_0)=k1_lattices(esk9_0,X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_59]), c_0_53])]), c_0_20])).
% 1.37/1.54  cnf(c_0_86, negated_conjecture, (k4_lattices(esk9_0,X1,esk10_0)=k2_lattices(esk9_0,X1,esk10_0)|~l1_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_59]), c_0_24])]), c_0_20])).
% 1.37/1.54  cnf(c_0_87, negated_conjecture, (k3_lattices(esk9_0,esk10_0,esk11_0)=k1_lattices(esk9_0,esk10_0,esk12_0)|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_72]), c_0_59])])).
% 1.37/1.54  cnf(c_0_88, negated_conjecture, (m1_subset_1(k2_lattices(esk9_0,esk11_0,esk11_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_29]), c_0_19])])).
% 1.37/1.54  cnf(c_0_89, negated_conjecture, (k1_lattices(esk9_0,esk11_0,X1)=k1_lattices(esk9_0,X1,esk11_0)|k1_lattices(esk9_0,X1,esk12_0)!=esk12_0|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_31])])).
% 1.37/1.54  cnf(c_0_90, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.37/1.54  cnf(c_0_91, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,X1,esk12_0),esk12_0)=esk12_0|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_23]), c_0_47]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_92, negated_conjecture, (k2_lattices(esk9_0,esk10_0,esk12_0)=k2_lattices(esk9_0,esk10_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_50]), c_0_59])])).
% 1.37/1.54  cnf(c_0_93, negated_conjecture, (m1_subset_1(k2_lattices(esk9_0,esk10_0,esk12_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_29]), c_0_19])])).
% 1.37/1.54  cnf(c_0_94, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,X1,k2_lattices(esk9_0,esk12_0,esk12_0)),k2_lattices(esk9_0,esk12_0,esk12_0))=k2_lattices(esk9_0,esk12_0,esk12_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_80]), c_0_47]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_95, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,X1,X2),k2_lattices(esk9_0,X1,esk12_0))=k2_lattices(esk9_0,X1,k1_lattices(esk9_0,X2,esk12_0))|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_23]), c_0_82]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_96, plain, (v2_struct_0(X1)|k1_lattices(X1,X2,X2)=X2|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 1.37/1.54  cnf(c_0_97, negated_conjecture, (k4_lattices(esk9_0,esk10_0,esk12_0)=k2_lattices(esk9_0,esk10_0,esk12_0)), inference(rw,[status(thm)],[c_0_58, c_0_69])).
% 1.37/1.54  cnf(c_0_98, negated_conjecture, (k1_lattices(esk9_0,esk12_0,X1)=k1_lattices(esk9_0,X1,esk12_0)|k1_lattices(esk9_0,X1,esk12_0)!=esk12_0|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_77]), c_0_23])])).
% 1.37/1.54  cnf(c_0_99, negated_conjecture, (k3_lattices(esk9_0,esk10_0,esk11_0)=k1_lattices(esk9_0,esk12_0,esk10_0)|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_73]), c_0_74]), c_0_23]), c_0_59])])).
% 1.37/1.54  cnf(c_0_100, negated_conjecture, (k4_lattices(esk9_0,X1,esk10_0)=k2_lattices(esk9_0,X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_29]), c_0_19])])).
% 1.37/1.54  cnf(c_0_101, negated_conjecture, (k1_lattices(esk9_0,esk10_0,esk12_0)=k1_lattices(esk9_0,esk10_0,esk11_0)|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_63]), c_0_59])])).
% 1.37/1.54  cnf(c_0_102, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,X1,X2),k2_lattices(esk9_0,X1,esk11_0))=k2_lattices(esk9_0,X1,k1_lattices(esk9_0,X2,esk11_0))|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_31]), c_0_82]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_103, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,X1,k2_lattices(esk9_0,esk11_0,esk11_0)),k2_lattices(esk9_0,esk11_0,esk11_0))=k2_lattices(esk9_0,esk11_0,esk11_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_88]), c_0_47]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_104, negated_conjecture, (k2_lattices(esk9_0,X1,esk11_0)=X1|~r1_lattices(esk9_0,X1,esk11_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_31]), c_0_46]), c_0_47]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_105, negated_conjecture, (r1_lattices(esk9_0,X1,esk11_0)|k1_lattices(esk9_0,X1,esk11_0)!=esk11_0|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_31]), c_0_20])).
% 1.37/1.54  cnf(c_0_106, negated_conjecture, (k1_lattices(esk9_0,esk11_0,X1)=k1_lattices(esk9_0,X1,esk11_0)|k1_lattices(esk9_0,X1,esk12_0)!=esk12_0|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_19])])).
% 1.37/1.54  cnf(c_0_107, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,esk10_0,esk11_0),esk12_0)=esk12_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_59])])).
% 1.37/1.54  cnf(c_0_108, negated_conjecture, (m1_subset_1(k2_lattices(esk9_0,esk10_0,esk11_0),u1_struct_0(esk9_0))), inference(rw,[status(thm)],[c_0_93, c_0_92])).
% 1.37/1.54  cnf(c_0_109, negated_conjecture, (k3_lattices(esk9_0,esk10_0,esk11_0)=k1_lattices(esk9_0,esk11_0,esk10_0)|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_64]), c_0_31]), c_0_59])])).
% 1.37/1.54  cnf(c_0_110, negated_conjecture, (k2_lattices(esk9_0,esk12_0,k1_lattices(esk9_0,k2_lattices(esk9_0,esk12_0,esk12_0),esk12_0))=k2_lattices(esk9_0,esk12_0,esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_23]), c_0_80])])).
% 1.37/1.54  cnf(c_0_111, negated_conjecture, (k1_lattices(esk9_0,esk12_0,esk12_0)=esk12_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_23]), c_0_46]), c_0_47]), c_0_24]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_112, negated_conjecture, (k4_lattices(esk9_0,esk10_0,esk12_0)=k2_lattices(esk9_0,esk10_0,esk11_0)), inference(rw,[status(thm)],[c_0_97, c_0_92])).
% 1.37/1.54  cnf(c_0_113, negated_conjecture, (k1_lattices(esk9_0,esk12_0,X1)=k1_lattices(esk9_0,X1,esk12_0)|k1_lattices(esk9_0,X1,esk12_0)!=esk12_0|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_90]), c_0_19])])).
% 1.37/1.54  cnf(c_0_114, negated_conjecture, (k1_lattices(esk9_0,esk12_0,esk10_0)=k1_lattices(esk9_0,esk10_0,esk11_0)|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_99]), c_0_59])])).
% 1.37/1.54  cnf(c_0_115, negated_conjecture, (k4_lattices(esk9_0,esk11_0,esk12_0)=k2_lattices(esk9_0,esk12_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_49]), c_0_23]), c_0_31])])).
% 1.37/1.54  cnf(c_0_116, negated_conjecture, (k2_lattices(esk9_0,esk11_0,esk10_0)=k2_lattices(esk9_0,esk10_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_51]), c_0_69]), c_0_92]), c_0_31]), c_0_59])])).
% 1.37/1.54  cnf(c_0_117, negated_conjecture, (k1_lattices(esk9_0,esk10_0,esk12_0)=k1_lattices(esk9_0,esk10_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_90]), c_0_19])])).
% 1.37/1.54  cnf(c_0_118, negated_conjecture, (k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,k2_lattices(esk9_0,esk11_0,esk11_0),esk11_0))=k2_lattices(esk9_0,esk11_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_88]), c_0_31])])).
% 1.37/1.54  cnf(c_0_119, negated_conjecture, (k2_lattices(esk9_0,X1,esk11_0)=X1|k1_lattices(esk9_0,X1,esk11_0)!=esk11_0|~m1_subset_1(X1,u1_struct_0(esk9_0))|~l2_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 1.37/1.54  cnf(c_0_120, negated_conjecture, (k1_lattices(esk9_0,esk11_0,esk11_0)=esk11_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_31]), c_0_46]), c_0_47]), c_0_24]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_121, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,X1,esk11_0),esk11_0)=esk11_0|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_31]), c_0_47]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_122, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,esk10_0,esk11_0),esk11_0)=k1_lattices(esk9_0,esk11_0,k2_lattices(esk9_0,esk10_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_108])])).
% 1.37/1.54  cnf(c_0_123, negated_conjecture, (k1_lattices(esk9_0,esk11_0,esk10_0)=k1_lattices(esk9_0,esk10_0,esk11_0)|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_109]), c_0_59])])).
% 1.37/1.54  cnf(c_0_124, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,X1,X2),k2_lattices(esk9_0,X1,esk10_0))=k2_lattices(esk9_0,X1,k1_lattices(esk9_0,X2,esk10_0))|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_59]), c_0_82]), c_0_19])]), c_0_20])).
% 1.37/1.54  cnf(c_0_125, negated_conjecture, (k2_lattices(esk9_0,esk12_0,esk12_0)=esk12_0|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_66]), c_0_111]), c_0_111]), c_0_23])])).
% 1.37/1.54  cnf(c_0_126, negated_conjecture, (k2_lattices(esk9_0,esk12_0,esk10_0)=k2_lattices(esk9_0,esk10_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_49]), c_0_112]), c_0_23]), c_0_59])])).
% 1.37/1.54  cnf(c_0_127, negated_conjecture, (k1_lattices(esk9_0,esk12_0,k2_lattices(esk9_0,esk10_0,esk11_0))=esk12_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_107]), c_0_108])])).
% 1.37/1.54  cnf(c_0_128, negated_conjecture, (k1_lattices(esk9_0,esk12_0,esk10_0)=k1_lattices(esk9_0,esk10_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_90]), c_0_19])])).
% 1.37/1.54  cnf(c_0_129, negated_conjecture, (k2_lattices(esk9_0,esk12_0,esk11_0)=k2_lattices(esk9_0,esk11_0,esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_115]), c_0_31])])).
% 1.37/1.54  cnf(c_0_130, negated_conjecture, (k1_lattices(esk9_0,k2_lattices(esk9_0,esk10_0,esk11_0),k2_lattices(esk9_0,esk11_0,esk12_0))=k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,esk10_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_116]), c_0_117]), c_0_59]), c_0_31])])).
% 1.37/1.54  cnf(c_0_131, negated_conjecture, (k2_lattices(esk9_0,esk11_0,esk11_0)=esk11_0|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120]), c_0_120]), c_0_31])])).
% 1.37/1.54  cnf(c_0_132, negated_conjecture, (k1_lattices(esk9_0,esk11_0,k2_lattices(esk9_0,esk10_0,esk11_0))=esk11_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_59])])).
% 1.37/1.54  cnf(c_0_133, negated_conjecture, (k1_lattices(esk9_0,esk11_0,esk10_0)=k1_lattices(esk9_0,esk10_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_90]), c_0_19])])).
% 1.37/1.54  cnf(c_0_134, negated_conjecture, (k2_lattices(esk9_0,esk12_0,k1_lattices(esk9_0,esk10_0,esk11_0))=esk12_0|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_126]), c_0_127]), c_0_128]), c_0_23])])).
% 1.37/1.54  cnf(c_0_135, negated_conjecture, (k2_lattices(esk9_0,esk12_0,k1_lattices(esk9_0,esk10_0,esk11_0))=k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,esk10_0,esk11_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_126]), c_0_129]), c_0_59]), c_0_23])]), c_0_130])).
% 1.37/1.54  cnf(c_0_136, negated_conjecture, (k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,esk10_0,esk11_0))=esk11_0|~l2_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_131]), c_0_116]), c_0_132]), c_0_133]), c_0_31])])).
% 1.37/1.54  cnf(c_0_137, negated_conjecture, (k2_lattices(esk9_0,esk11_0,k1_lattices(esk9_0,esk10_0,esk11_0))=esk12_0|~l2_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_134, c_0_135])).
% 1.37/1.54  cnf(c_0_138, negated_conjecture, (esk11_0!=esk12_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.54  cnf(c_0_139, negated_conjecture, (~l2_lattices(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_138])).
% 1.37/1.54  cnf(c_0_140, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_90]), c_0_19])]), ['proof']).
% 1.37/1.54  # SZS output end CNFRefutation
% 1.37/1.54  # Proof object total steps             : 141
% 1.37/1.54  # Proof object clause steps            : 114
% 1.37/1.54  # Proof object formula steps           : 27
% 1.37/1.54  # Proof object conjectures             : 101
% 1.37/1.54  # Proof object clause conjectures      : 98
% 1.37/1.54  # Proof object formula conjectures     : 3
% 1.37/1.54  # Proof object initial clauses used    : 26
% 1.37/1.54  # Proof object initial formulas used   : 13
% 1.37/1.54  # Proof object generating inferences   : 84
% 1.37/1.54  # Proof object simplifying inferences  : 227
% 1.37/1.54  # Training examples: 0 positive, 0 negative
% 1.37/1.54  # Parsed axioms                        : 14
% 1.37/1.54  # Removed by relevancy pruning/SinE    : 0
% 1.37/1.54  # Initial clauses                      : 43
% 1.37/1.54  # Removed in clause preprocessing      : 1
% 1.37/1.54  # Initial clauses in saturation        : 42
% 1.37/1.54  # Processed clauses                    : 8820
% 1.37/1.54  # ...of these trivial                  : 157
% 1.37/1.54  # ...subsumed                          : 7044
% 1.37/1.54  # ...remaining for further processing  : 1619
% 1.37/1.54  # Other redundant clauses eliminated   : 116
% 1.37/1.54  # Clauses deleted for lack of memory   : 0
% 1.37/1.54  # Backward-subsumed                    : 196
% 1.37/1.54  # Backward-rewritten                   : 51
% 1.37/1.54  # Generated clauses                    : 100345
% 1.37/1.54  # ...of the previous two non-trivial   : 91361
% 1.37/1.54  # Contextual simplify-reflections      : 10
% 1.37/1.54  # Paramodulations                      : 100229
% 1.37/1.54  # Factorizations                       : 0
% 1.37/1.54  # Equation resolutions                 : 116
% 1.37/1.54  # Propositional unsat checks           : 0
% 1.37/1.54  #    Propositional check models        : 0
% 1.37/1.54  #    Propositional check unsatisfiable : 0
% 1.37/1.54  #    Propositional clauses             : 0
% 1.37/1.54  #    Propositional clauses after purity: 0
% 1.37/1.54  #    Propositional unsat core size     : 0
% 1.37/1.54  #    Propositional preprocessing time  : 0.000
% 1.37/1.54  #    Propositional encoding time       : 0.000
% 1.37/1.54  #    Propositional solver time         : 0.000
% 1.37/1.54  #    Success case prop preproc time    : 0.000
% 1.37/1.54  #    Success case prop encoding time   : 0.000
% 1.37/1.54  #    Success case prop solver time     : 0.000
% 1.37/1.54  # Current number of processed clauses  : 1330
% 1.37/1.54  #    Positive orientable unit clauses  : 58
% 1.37/1.54  #    Positive unorientable unit clauses: 0
% 1.37/1.54  #    Negative unit clauses             : 7
% 1.37/1.54  #    Non-unit-clauses                  : 1265
% 1.37/1.54  # Current number of unprocessed clauses: 82424
% 1.37/1.54  # ...number of literals in the above   : 471857
% 1.37/1.54  # Current number of archived formulas  : 0
% 1.37/1.54  # Current number of archived clauses   : 289
% 1.37/1.54  # Clause-clause subsumption calls (NU) : 200042
% 1.37/1.54  # Rec. Clause-clause subsumption calls : 84558
% 1.37/1.54  # Non-unit clause-clause subsumptions  : 4656
% 1.37/1.54  # Unit Clause-clause subsumption calls : 1043
% 1.37/1.54  # Rewrite failures with RHS unbound    : 0
% 1.37/1.54  # BW rewrite match attempts            : 314
% 1.37/1.54  # BW rewrite match successes           : 22
% 1.37/1.54  # Condensation attempts                : 0
% 1.37/1.54  # Condensation successes               : 0
% 1.37/1.54  # Termbank termtop insertions          : 3814117
% 1.37/1.54  
% 1.37/1.54  # -------------------------------------------------
% 1.37/1.54  # User time                : 1.144 s
% 1.37/1.54  # System time              : 0.057 s
% 1.37/1.54  # Total time               : 1.201 s
% 1.37/1.54  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
