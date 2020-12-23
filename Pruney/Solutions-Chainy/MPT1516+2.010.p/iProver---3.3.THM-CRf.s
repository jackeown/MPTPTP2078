%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:18 EST 2020

% Result     : Theorem 31.64s
% Output     : CNFRefutation 31.64s
% Verified   : 
% Statistics : Number of formulae       :  316 (3853 expanded)
%              Number of clauses        :  203 (1156 expanded)
%              Number of leaves         :   31 ( 754 expanded)
%              Depth                    :   31
%              Number of atoms          : 1520 (25094 expanded)
%              Number of equality atoms :  384 (3279 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f51,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f83,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
        | ~ l3_lattices(sK9)
        | ~ v13_lattices(sK9)
        | ~ v10_lattices(sK9)
        | v2_struct_0(sK9) )
      & l3_lattices(sK9)
      & v4_lattice3(sK9)
      & v10_lattices(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,
    ( ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
      | ~ l3_lattices(sK9)
      | ~ v13_lattices(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) )
    & l3_lattices(sK9)
    & v4_lattice3(sK9)
    & v10_lattices(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f52,f83])).

fof(f128,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f84])).

fof(f131,plain,(
    l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f84])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f96,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f58])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( k2_lattices(X0,X4,sK2(X0)) = sK2(X0)
              & k2_lattices(X0,sK2(X0),X4) = sK2(X0) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( k2_lattices(X0,X4,sK2(X0)) = sK2(X0)
                  & k2_lattices(X0,sK2(X0),X4) = sK2(X0) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f59,f61,f60])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f130,plain,(
    v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f84])).

fof(f129,plain,(
    v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f84])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = X1
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f67])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK5(X0)) != k2_lattices(X0,sK5(X0),X1)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,X2,sK4(X0)) != k2_lattices(X0,sK4(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f68,f70,f69])).

fof(f108,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f24,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f24])).

fof(f88,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f132,plain,
    ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
    | ~ l3_lattices(sK9)
    | ~ v13_lattices(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f84])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f133,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f43])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattices(X1,X2,X3)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattices(X1,X2,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f72])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X2,X4)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,sK6(X0,X1,X2))
        & sK6(X0,X1,X2) = X0
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,X2,sK6(X0,X1,X2))
            & sK6(X0,X1,X2) = X0
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f73,f74])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ r3_lattices(X1,X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f135,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_4_lattice3(X1,X2))
      | ~ r3_lattices(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f117])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f77])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK7(X0,X1,X2),X1)
        & r3_lattice3(X0,sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK7(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK7(X0,X1,X2),X2)
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f78,f79])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f137,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f81,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r2_hidden(X4,X2)
            | ~ r3_lattices(X0,sK8(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK8(X0,X1,X2),X1)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X0,sK8(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(sK8(X0,X1,X2),X1)
            & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f81])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
                  & r2_hidden(sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f64,f65])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f90,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1957,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_47])).

cnf(c_1958,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
    | ~ l3_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1957])).

cnf(c_44,negated_conjecture,
    ( l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1962,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1958,c_44])).

cnf(c_4147,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_1962])).

cnf(c_4804,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4147])).

cnf(c_11,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1015,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v13_lattices(X1)
    | ~ l3_lattices(X2)
    | v2_struct_0(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_1016,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_1015])).

cnf(c_2131,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v13_lattices(X1)
    | ~ l3_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1016,c_47])).

cnf(c_2132,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | m1_subset_1(sK1(sK9,X0),u1_struct_0(sK9))
    | v13_lattices(sK9)
    | ~ l3_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_2131])).

cnf(c_2136,plain,
    ( v13_lattices(sK9)
    | m1_subset_1(sK1(sK9,X0),u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2132,c_44])).

cnf(c_2137,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | m1_subset_1(sK1(sK9,X0),u1_struct_0(sK9))
    | v13_lattices(sK9) ),
    inference(renaming,[status(thm)],[c_2136])).

cnf(c_4139,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | m1_subset_1(sK1(sK9,X0_62),u1_struct_0(sK9))
    | v13_lattices(sK9) ),
    inference(subtyping,[status(esa)],[c_2137])).

cnf(c_4812,plain,
    ( m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK1(sK9,X0_62),u1_struct_0(sK9)) = iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4139])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_45,negated_conjecture,
    ( v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_45])).

cnf(c_1363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k15_lattice3(sK9,a_2_3_lattice3(sK9,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1362])).

cnf(c_46,negated_conjecture,
    ( v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k15_lattice3(sK9,a_2_3_lattice3(sK9,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1363,c_47,c_46,c_44])).

cnf(c_4167,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | k15_lattice3(sK9,a_2_3_lattice3(sK9,X0_62)) = X0_62 ),
    inference(subtyping,[status(esa)],[c_1367])).

cnf(c_4784,plain,
    ( k15_lattice3(sK9,a_2_3_lattice3(sK9,X0_62)) = X0_62
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4167])).

cnf(c_7251,plain,
    ( k15_lattice3(sK9,a_2_3_lattice3(sK9,sK1(sK9,X0_62))) = sK1(sK9,X0_62)
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4812,c_4784])).

cnf(c_10643,plain,
    ( k15_lattice3(sK9,a_2_3_lattice3(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)))) = sK1(sK9,k15_lattice3(sK9,X0_63))
    | v13_lattices(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4804,c_7251])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k5_lattices(X1) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X2)
    | v2_struct_0(X1)
    | X1 != X2
    | k5_lattices(X1) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_7])).

cnf(c_1111,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k5_lattices(X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1110])).

cnf(c_2041,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | k5_lattices(X1) = X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1111,c_47])).

cnf(c_2042,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | m1_subset_1(sK0(sK9,X0),u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | ~ l3_lattices(sK9)
    | k5_lattices(sK9) = X0 ),
    inference(unflattening,[status(thm)],[c_2041])).

cnf(c_2046,plain,
    ( ~ v13_lattices(sK9)
    | m1_subset_1(sK0(sK9,X0),u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k5_lattices(sK9) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2042,c_44])).

cnf(c_2047,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | m1_subset_1(sK0(sK9,X0),u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | k5_lattices(sK9) = X0 ),
    inference(renaming,[status(thm)],[c_2046])).

cnf(c_4143,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | m1_subset_1(sK0(sK9,X0_62),u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | k5_lattices(sK9) = X0_62 ),
    inference(subtyping,[status(esa)],[c_2047])).

cnf(c_4808,plain,
    ( k5_lattices(sK9) = X0_62
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK0(sK9,X0_62),u1_struct_0(sK9)) = iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4143])).

cnf(c_10,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_935,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_10])).

cnf(c_1891,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_935,c_47])).

cnf(c_1892,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | ~ l3_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1891])).

cnf(c_147,plain,
    ( l1_lattices(sK9)
    | ~ l3_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_150,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | ~ l1_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1894,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1892,c_47,c_44,c_147,c_150])).

cnf(c_4151,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_1894])).

cnf(c_4800,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4151])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_949,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_950,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_949])).

cnf(c_2194,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_950,c_47])).

cnf(c_2195,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ v6_lattices(sK9)
    | ~ l3_lattices(sK9)
    | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
    inference(unflattening,[status(thm)],[c_2194])).

cnf(c_4,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1760,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_46])).

cnf(c_1761,plain,
    ( v6_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_1760])).

cnf(c_166,plain,
    ( v6_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1763,plain,
    ( v6_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1761,c_47,c_46,c_44,c_166])).

cnf(c_1849,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_950,c_1763])).

cnf(c_1850,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1849])).

cnf(c_1854,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1850,c_47,c_44])).

cnf(c_2198,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2195,c_47,c_44,c_1850])).

cnf(c_4152,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_62,u1_struct_0(sK9))
    | k2_lattices(sK9,X0_62,X1_62) = k2_lattices(sK9,X1_62,X0_62) ),
    inference(subtyping,[status(esa)],[c_2198])).

cnf(c_4799,plain,
    ( k2_lattices(sK9,X0_62,X1_62) = k2_lattices(sK9,X1_62,X0_62)
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4152])).

cnf(c_5654,plain,
    ( k2_lattices(sK9,X0_62,k5_lattices(sK9)) = k2_lattices(sK9,k5_lattices(sK9),X0_62)
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4800,c_4799])).

cnf(c_9341,plain,
    ( k2_lattices(sK9,sK0(sK9,X0_62),k5_lattices(sK9)) = k2_lattices(sK9,k5_lattices(sK9),sK0(sK9,X0_62))
    | k5_lattices(sK9) = X0_62
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4808,c_5654])).

cnf(c_76056,plain,
    ( k2_lattices(sK9,k5_lattices(sK9),sK0(sK9,k15_lattice3(sK9,X0_63))) = k2_lattices(sK9,sK0(sK9,k15_lattice3(sK9,X0_63)),k5_lattices(sK9))
    | k15_lattice3(sK9,X0_63) = k5_lattices(sK9)
    | v13_lattices(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4804,c_9341])).

cnf(c_4178,plain,
    ( X0_63 != X1_63
    | k15_lattice3(X0_61,X0_63) = k15_lattice3(X0_61,X1_63) ),
    theory(equality)).

cnf(c_4185,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k15_lattice3(sK9,k1_xboole_0) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4178])).

cnf(c_4172,plain,
    ( X0_63 = X0_63 ),
    theory(equality)).

cnf(c_4190,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4172])).

cnf(c_43,negated_conjecture,
    ( ~ v13_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_281,negated_conjecture,
    ( ~ v13_lattices(sK9)
    | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_43,c_47,c_46,c_44])).

cnf(c_4169,negated_conjecture,
    ( ~ v13_lattices(sK9)
    | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_281])).

cnf(c_4191,plain,
    ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
    | v13_lattices(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4169])).

cnf(c_4246,plain,
    ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_4147])).

cnf(c_4245,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4147])).

cnf(c_4247,plain,
    ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4245])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1085,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X2)
    | v2_struct_0(X1)
    | X1 != X2
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_8])).

cnf(c_1086,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
    inference(unflattening,[status(thm)],[c_1085])).

cnf(c_1096,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1086,c_935])).

cnf(c_2065,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1096,c_47])).

cnf(c_2066,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | ~ l3_lattices(sK9)
    | k2_lattices(sK9,X0,k5_lattices(sK9)) = k5_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_2065])).

cnf(c_2070,plain,
    ( ~ v13_lattices(sK9)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,k5_lattices(sK9)) = k5_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2066,c_44])).

cnf(c_2071,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | k2_lattices(sK9,X0,k5_lattices(sK9)) = k5_lattices(sK9) ),
    inference(renaming,[status(thm)],[c_2070])).

cnf(c_4142,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | k2_lattices(sK9,X0_62,k5_lattices(sK9)) = k5_lattices(sK9) ),
    inference(subtyping,[status(esa)],[c_2071])).

cnf(c_5335,plain,
    ( ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) = k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_4142])).

cnf(c_5336,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) = k5_lattices(sK9)
    | m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5335])).

cnf(c_5338,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) = k5_lattices(sK9)
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5336])).

cnf(c_4173,plain,
    ( X0_62 != X1_62
    | X2_62 != X1_62
    | X2_62 = X0_62 ),
    theory(equality)).

cnf(c_5188,plain,
    ( k15_lattice3(sK9,k1_xboole_0) != X0_62
    | k5_lattices(sK9) != X0_62
    | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_5551,plain,
    ( k15_lattice3(sK9,k1_xboole_0) != k5_lattices(sK9)
    | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0)
    | k5_lattices(sK9) != k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_5188])).

cnf(c_29,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X2,a_2_4_lattice3(X0,X1))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1632,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,a_2_4_lattice3(X0,X1))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_45])).

cnf(c_1633,plain,
    ( ~ r3_lattices(sK9,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | r2_hidden(X1,a_2_4_lattice3(sK9,X0))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1632])).

cnf(c_1637,plain,
    ( r2_hidden(X1,a_2_4_lattice3(sK9,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r3_lattices(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1633,c_47,c_46,c_44])).

cnf(c_1638,plain,
    ( ~ r3_lattices(sK9,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | r2_hidden(X1,a_2_4_lattice3(sK9,X0)) ),
    inference(renaming,[status(thm)],[c_1637])).

cnf(c_4155,plain,
    ( ~ r3_lattices(sK9,X0_62,X1_62)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_62,u1_struct_0(sK9))
    | r2_hidden(X1_62,a_2_4_lattice3(sK9,X0_62)) ),
    inference(subtyping,[status(esa)],[c_1638])).

cnf(c_4980,plain,
    ( ~ r3_lattices(sK9,k15_lattice3(sK9,X0_63),X0_62)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
    | r2_hidden(X0_62,a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) ),
    inference(instantiation,[status(thm)],[c_4155])).

cnf(c_6294,plain,
    ( ~ r3_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9))
    | ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
    | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | r2_hidden(k5_lattices(sK9),a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) ),
    inference(instantiation,[status(thm)],[c_4980])).

cnf(c_6296,plain,
    ( ~ r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9))
    | ~ m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9))
    | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | r2_hidden(k5_lattices(sK9),a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_6294])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k16_lattice3(X1,a_2_4_lattice3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1380,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k16_lattice3(X1,a_2_4_lattice3(X1,X0)) = X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_45])).

cnf(c_1381,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k16_lattice3(sK9,a_2_4_lattice3(sK9,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1380])).

cnf(c_1385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k16_lattice3(sK9,a_2_4_lattice3(sK9,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1381,c_47,c_46,c_44])).

cnf(c_4166,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)) = X0_62 ),
    inference(subtyping,[status(esa)],[c_1385])).

cnf(c_4785,plain,
    ( k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)) = X0_62
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4166])).

cnf(c_5326,plain,
    ( k16_lattice3(sK9,a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) = k15_lattice3(sK9,X0_63) ),
    inference(superposition,[status(thm)],[c_4804,c_4785])).

cnf(c_37,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_28,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_291,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37,c_28])).

cnf(c_1440,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_291,c_45])).

cnf(c_1441,plain,
    ( r3_lattice3(sK9,k16_lattice3(sK9,X0),X0)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1440])).

cnf(c_1445,plain,
    ( r3_lattice3(sK9,k16_lattice3(sK9,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1441,c_47,c_46,c_44])).

cnf(c_4163,plain,
    ( r3_lattice3(sK9,k16_lattice3(sK9,X0_63),X0_63) ),
    inference(subtyping,[status(esa)],[c_1445])).

cnf(c_4788,plain,
    ( r3_lattice3(sK9,k16_lattice3(sK9,X0_63),X0_63) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4163])).

cnf(c_6382,plain,
    ( r3_lattice3(sK9,k15_lattice3(sK9,X0_63),a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5326,c_4788])).

cnf(c_6385,plain,
    ( r3_lattice3(sK9,k15_lattice3(sK9,X0_63),a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6382])).

cnf(c_6387,plain,
    ( r3_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0),a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_6385])).

cnf(c_4171,plain,
    ( X0_62 = X0_62 ),
    theory(equality)).

cnf(c_6586,plain,
    ( k5_lattices(sK9) = k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_4171])).

cnf(c_5317,plain,
    ( k15_lattice3(sK9,a_2_3_lattice3(sK9,k5_lattices(sK9))) = k5_lattices(sK9) ),
    inference(superposition,[status(thm)],[c_4800,c_4784])).

cnf(c_41,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK8(X0,X1,X2),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1473,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK8(X0,X1,X2),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_45])).

cnf(c_1474,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1))
    | r2_hidden(sK8(sK9,X0,X1),X0)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1473])).

cnf(c_1478,plain,
    ( r2_hidden(sK8(sK9,X0,X1),X0)
    | r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1474,c_47,c_46,c_44])).

cnf(c_1479,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1))
    | r2_hidden(sK8(sK9,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_1478])).

cnf(c_4161,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,X0_63),k15_lattice3(sK9,X1_63))
    | r2_hidden(sK8(sK9,X0_63,X1_63),X0_63) ),
    inference(subtyping,[status(esa)],[c_1479])).

cnf(c_4790,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,X0_63),k15_lattice3(sK9,X1_63)) = iProver_top
    | r2_hidden(sK8(sK9,X0_63,X1_63),X0_63) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4161])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_542,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_543,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_4168,plain,
    ( ~ r2_hidden(X0_62,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_543])).

cnf(c_4783,plain,
    ( r2_hidden(X0_62,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4168])).

cnf(c_7218,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0_63)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4790,c_4783])).

cnf(c_7429,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5317,c_7218])).

cnf(c_7432,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7429])).

cnf(c_5552,plain,
    ( X0_62 != X1_62
    | k5_lattices(sK9) != X1_62
    | k5_lattices(sK9) = X0_62 ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_7048,plain,
    ( X0_62 != k5_lattices(sK9)
    | k5_lattices(sK9) = X0_62
    | k5_lattices(sK9) != k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_5552])).

cnf(c_9016,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) != k5_lattices(sK9)
    | k5_lattices(sK9) = k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9))
    | k5_lattices(sK9) != k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_7048])).

cnf(c_9022,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) != k5_lattices(sK9)
    | k5_lattices(sK9) = k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9))
    | k5_lattices(sK9) != k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_9016])).

cnf(c_22,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_13,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_553,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(resolution,[status(thm)],[c_2,c_13])).

cnf(c_3,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_lattices(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_3])).

cnf(c_558,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(renaming,[status(thm)],[c_557])).

cnf(c_759,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X6,u1_struct_0(X5))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | ~ v10_lattices(X5)
    | X6 != X3
    | X4 != X1
    | X5 != X0
    | k2_lattices(X5,X4,X6) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_558])).

cnf(c_760,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X3) = X1 ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_1733,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X3) = X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_760,c_46])).

cnf(c_1734,plain,
    ( ~ r3_lattice3(sK9,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k2_lattices(sK9,X0,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_1733])).

cnf(c_1738,plain,
    ( ~ r3_lattice3(sK9,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ r2_hidden(X2,X1)
    | k2_lattices(sK9,X0,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1734,c_47,c_44])).

cnf(c_1739,plain,
    ( ~ r3_lattice3(sK9,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ r2_hidden(X2,X1)
    | k2_lattices(sK9,X0,X2) = X0 ),
    inference(renaming,[status(thm)],[c_1738])).

cnf(c_4153,plain,
    ( ~ r3_lattice3(sK9,X0_62,X0_63)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | ~ m1_subset_1(X1_62,u1_struct_0(sK9))
    | ~ r2_hidden(X1_62,X0_63)
    | k2_lattices(sK9,X0_62,X1_62) = X0_62 ),
    inference(subtyping,[status(esa)],[c_1739])).

cnf(c_5181,plain,
    ( ~ r3_lattice3(sK9,k15_lattice3(sK9,X0_63),X1_63)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
    | ~ r2_hidden(X0_62,X1_63)
    | k2_lattices(sK9,k15_lattice3(sK9,X0_63),X0_62) = k15_lattice3(sK9,X0_63) ),
    inference(instantiation,[status(thm)],[c_4153])).

cnf(c_13757,plain,
    ( ~ r3_lattice3(sK9,k15_lattice3(sK9,X0_63),a_2_4_lattice3(sK9,k15_lattice3(sK9,X1_63)))
    | ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
    | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | ~ r2_hidden(k5_lattices(sK9),a_2_4_lattice3(sK9,k15_lattice3(sK9,X1_63)))
    | k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) = k15_lattice3(sK9,X0_63) ),
    inference(instantiation,[status(thm)],[c_5181])).

cnf(c_13759,plain,
    ( ~ r3_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0),a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9))
    | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | ~ r2_hidden(k5_lattices(sK9),a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0)))
    | k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13757])).

cnf(c_11613,plain,
    ( X0_62 != X1_62
    | k15_lattice3(sK9,X0_63) != X1_62
    | k15_lattice3(sK9,X0_63) = X0_62 ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_21345,plain,
    ( X0_62 != k15_lattice3(sK9,X0_63)
    | k15_lattice3(sK9,X1_63) = X0_62
    | k15_lattice3(sK9,X1_63) != k15_lattice3(sK9,X0_63) ),
    inference(instantiation,[status(thm)],[c_11613])).

cnf(c_46425,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) != k15_lattice3(sK9,X0_63)
    | k15_lattice3(sK9,X1_63) = k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9))
    | k15_lattice3(sK9,X1_63) != k15_lattice3(sK9,X0_63) ),
    inference(instantiation,[status(thm)],[c_21345])).

cnf(c_46426,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) != k15_lattice3(sK9,k1_xboole_0)
    | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9))
    | k15_lattice3(sK9,k1_xboole_0) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_46425])).

cnf(c_7200,plain,
    ( X0_62 != X1_62
    | X0_62 = k5_lattices(sK9)
    | k5_lattices(sK9) != X1_62 ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_41390,plain,
    ( k15_lattice3(sK9,k1_xboole_0) != X0_62
    | k15_lattice3(sK9,k1_xboole_0) = k5_lattices(sK9)
    | k5_lattices(sK9) != X0_62 ),
    inference(instantiation,[status(thm)],[c_7200])).

cnf(c_76491,plain,
    ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9))
    | k15_lattice3(sK9,k1_xboole_0) = k5_lattices(sK9)
    | k5_lattices(sK9) != k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) ),
    inference(instantiation,[status(thm)],[c_41390])).

cnf(c_76492,plain,
    ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9))
    | k15_lattice3(sK9,k1_xboole_0) = k5_lattices(sK9)
    | k5_lattices(sK9) != k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) ),
    inference(instantiation,[status(thm)],[c_76491])).

cnf(c_76563,plain,
    ( v13_lattices(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_76056,c_47,c_44,c_147,c_150,c_4185,c_4190,c_4191,c_4246,c_4247,c_5338,c_5551,c_6296,c_6387,c_6586,c_7432,c_9022,c_13759,c_46426,c_76492])).

cnf(c_76571,plain,
    ( k15_lattice3(sK9,a_2_3_lattice3(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)))) = sK1(sK9,k15_lattice3(sK9,X0_63)) ),
    inference(superposition,[status(thm)],[c_10643,c_76563])).

cnf(c_1942,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_47])).

cnf(c_1943,plain,
    ( m1_subset_1(k16_lattice3(sK9,X0),u1_struct_0(sK9))
    | ~ l3_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1942])).

cnf(c_1947,plain,
    ( m1_subset_1(k16_lattice3(sK9,X0),u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1943,c_44])).

cnf(c_4148,plain,
    ( m1_subset_1(k16_lattice3(sK9,X0_63),u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_1947])).

cnf(c_4803,plain,
    ( m1_subset_1(k16_lattice3(sK9,X0_63),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4148])).

cnf(c_4796,plain,
    ( r3_lattices(sK9,X0_62,X1_62) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1_62,a_2_4_lattice3(sK9,X0_62)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4155])).

cnf(c_4798,plain,
    ( k2_lattices(sK9,X0_62,X1_62) = X0_62
    | r3_lattice3(sK9,X0_62,X0_63) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1_62,X0_63) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4153])).

cnf(c_7029,plain,
    ( k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = X0_62
    | r3_lattice3(sK9,X0_62,X1_63) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(k15_lattice3(sK9,X0_63),X1_63) != iProver_top ),
    inference(superposition,[status(thm)],[c_4804,c_4798])).

cnf(c_9775,plain,
    ( k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = X0_62
    | r3_lattices(sK9,X1_62,k15_lattice3(sK9,X0_63)) != iProver_top
    | r3_lattice3(sK9,X0_62,a_2_4_lattice3(sK9,X1_62)) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4796,c_7029])).

cnf(c_22885,plain,
    ( m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
    | r3_lattice3(sK9,X0_62,a_2_4_lattice3(sK9,X1_62)) != iProver_top
    | r3_lattices(sK9,X1_62,k15_lattice3(sK9,X0_63)) != iProver_top
    | k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = X0_62 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9775,c_4245])).

cnf(c_22886,plain,
    ( k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = X0_62
    | r3_lattices(sK9,X1_62,k15_lattice3(sK9,X0_63)) != iProver_top
    | r3_lattice3(sK9,X0_62,a_2_4_lattice3(sK9,X1_62)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22885])).

cnf(c_22892,plain,
    ( k2_lattices(sK9,k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)),k15_lattice3(sK9,X0_63)) = k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62))
    | r3_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_22886])).

cnf(c_22946,plain,
    ( k2_lattices(sK9,k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)),k15_lattice3(sK9,X0_63)) = k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62))
    | r3_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_22892])).

cnf(c_22963,plain,
    ( k2_lattices(sK9,k16_lattice3(sK9,a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0))),k15_lattice3(sK9,X0_63)) = k16_lattice3(sK9,a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0)))
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7218,c_22946])).

cnf(c_22979,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0_63)) = k15_lattice3(sK9,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22963,c_5326])).

cnf(c_44639,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0_63)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22979,c_4247])).

cnf(c_90394,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,X0_63))) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_76571,c_44639])).

cnf(c_90518,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_90394])).

cnf(c_5655,plain,
    ( k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = k2_lattices(sK9,k15_lattice3(sK9,X0_63),X0_62)
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4804,c_4799])).

cnf(c_9396,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k15_lattice3(sK9,X1_63)) = k2_lattices(sK9,k15_lattice3(sK9,X1_63),k15_lattice3(sK9,X0_63)) ),
    inference(superposition,[status(thm)],[c_4804,c_5655])).

cnf(c_44647,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_44639,c_9396])).

cnf(c_90393,plain,
    ( k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_76571,c_44647])).

cnf(c_90517,plain,
    ( k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_90393])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1036,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v13_lattices(X1)
    | ~ l3_lattices(X2)
    | v2_struct_0(X1)
    | X1 != X2
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_1037,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
    inference(unflattening,[status(thm)],[c_1036])).

cnf(c_2107,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v13_lattices(X1)
    | ~ l3_lattices(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1037,c_47])).

cnf(c_2108,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | v13_lattices(sK9)
    | ~ l3_lattices(sK9)
    | k2_lattices(sK9,X0,sK1(sK9,X0)) != X0
    | k2_lattices(sK9,sK1(sK9,X0),X0) != X0 ),
    inference(unflattening,[status(thm)],[c_2107])).

cnf(c_2112,plain,
    ( v13_lattices(sK9)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,sK1(sK9,X0)) != X0
    | k2_lattices(sK9,sK1(sK9,X0),X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2108,c_44])).

cnf(c_2113,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | v13_lattices(sK9)
    | k2_lattices(sK9,X0,sK1(sK9,X0)) != X0
    | k2_lattices(sK9,sK1(sK9,X0),X0) != X0 ),
    inference(renaming,[status(thm)],[c_2112])).

cnf(c_4140,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
    | v13_lattices(sK9)
    | k2_lattices(sK9,X0_62,sK1(sK9,X0_62)) != X0_62
    | k2_lattices(sK9,sK1(sK9,X0_62),X0_62) != X0_62 ),
    inference(subtyping,[status(esa)],[c_2113])).

cnf(c_5026,plain,
    ( ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
    | v13_lattices(sK9)
    | k2_lattices(sK9,k15_lattice3(sK9,X0_63),sK1(sK9,k15_lattice3(sK9,X0_63))) != k15_lattice3(sK9,X0_63)
    | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)),k15_lattice3(sK9,X0_63)) != k15_lattice3(sK9,X0_63) ),
    inference(instantiation,[status(thm)],[c_4140])).

cnf(c_5027,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),sK1(sK9,k15_lattice3(sK9,X0_63))) != k15_lattice3(sK9,X0_63)
    | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)),k15_lattice3(sK9,X0_63)) != k15_lattice3(sK9,X0_63)
    | m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5026])).

cnf(c_5029,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) != k15_lattice3(sK9,k1_xboole_0)
    | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) != k15_lattice3(sK9,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5027])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_90518,c_90517,c_76563,c_5029,c_4247])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:31:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 31.64/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.64/4.49  
% 31.64/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.64/4.49  
% 31.64/4.49  ------  iProver source info
% 31.64/4.49  
% 31.64/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.64/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.64/4.49  git: non_committed_changes: false
% 31.64/4.49  git: last_make_outside_of_git: false
% 31.64/4.49  
% 31.64/4.49  ------ 
% 31.64/4.49  
% 31.64/4.49  ------ Input Options
% 31.64/4.49  
% 31.64/4.49  --out_options                           all
% 31.64/4.49  --tptp_safe_out                         true
% 31.64/4.49  --problem_path                          ""
% 31.64/4.49  --include_path                          ""
% 31.64/4.49  --clausifier                            res/vclausify_rel
% 31.64/4.49  --clausifier_options                    ""
% 31.64/4.49  --stdin                                 false
% 31.64/4.49  --stats_out                             all
% 31.64/4.49  
% 31.64/4.49  ------ General Options
% 31.64/4.49  
% 31.64/4.49  --fof                                   false
% 31.64/4.49  --time_out_real                         305.
% 31.64/4.49  --time_out_virtual                      -1.
% 31.64/4.49  --symbol_type_check                     false
% 31.64/4.49  --clausify_out                          false
% 31.64/4.49  --sig_cnt_out                           false
% 31.64/4.49  --trig_cnt_out                          false
% 31.64/4.49  --trig_cnt_out_tolerance                1.
% 31.64/4.49  --trig_cnt_out_sk_spl                   false
% 31.64/4.49  --abstr_cl_out                          false
% 31.64/4.49  
% 31.64/4.49  ------ Global Options
% 31.64/4.49  
% 31.64/4.49  --schedule                              default
% 31.64/4.49  --add_important_lit                     false
% 31.64/4.49  --prop_solver_per_cl                    1000
% 31.64/4.49  --min_unsat_core                        false
% 31.64/4.49  --soft_assumptions                      false
% 31.64/4.49  --soft_lemma_size                       3
% 31.64/4.49  --prop_impl_unit_size                   0
% 31.64/4.49  --prop_impl_unit                        []
% 31.64/4.49  --share_sel_clauses                     true
% 31.64/4.49  --reset_solvers                         false
% 31.64/4.49  --bc_imp_inh                            [conj_cone]
% 31.64/4.49  --conj_cone_tolerance                   3.
% 31.64/4.49  --extra_neg_conj                        none
% 31.64/4.49  --large_theory_mode                     true
% 31.64/4.49  --prolific_symb_bound                   200
% 31.64/4.49  --lt_threshold                          2000
% 31.64/4.49  --clause_weak_htbl                      true
% 31.64/4.49  --gc_record_bc_elim                     false
% 31.64/4.49  
% 31.64/4.49  ------ Preprocessing Options
% 31.64/4.49  
% 31.64/4.49  --preprocessing_flag                    true
% 31.64/4.49  --time_out_prep_mult                    0.1
% 31.64/4.49  --splitting_mode                        input
% 31.64/4.49  --splitting_grd                         true
% 31.64/4.49  --splitting_cvd                         false
% 31.64/4.49  --splitting_cvd_svl                     false
% 31.64/4.49  --splitting_nvd                         32
% 31.64/4.49  --sub_typing                            true
% 31.64/4.49  --prep_gs_sim                           true
% 31.64/4.49  --prep_unflatten                        true
% 31.64/4.49  --prep_res_sim                          true
% 31.64/4.49  --prep_upred                            true
% 31.64/4.49  --prep_sem_filter                       exhaustive
% 31.64/4.49  --prep_sem_filter_out                   false
% 31.64/4.49  --pred_elim                             true
% 31.64/4.49  --res_sim_input                         true
% 31.64/4.49  --eq_ax_congr_red                       true
% 31.64/4.49  --pure_diseq_elim                       true
% 31.64/4.49  --brand_transform                       false
% 31.64/4.49  --non_eq_to_eq                          false
% 31.64/4.49  --prep_def_merge                        true
% 31.64/4.49  --prep_def_merge_prop_impl              false
% 31.64/4.49  --prep_def_merge_mbd                    true
% 31.64/4.49  --prep_def_merge_tr_red                 false
% 31.64/4.49  --prep_def_merge_tr_cl                  false
% 31.64/4.49  --smt_preprocessing                     true
% 31.64/4.49  --smt_ac_axioms                         fast
% 31.64/4.49  --preprocessed_out                      false
% 31.64/4.49  --preprocessed_stats                    false
% 31.64/4.49  
% 31.64/4.49  ------ Abstraction refinement Options
% 31.64/4.49  
% 31.64/4.49  --abstr_ref                             []
% 31.64/4.49  --abstr_ref_prep                        false
% 31.64/4.49  --abstr_ref_until_sat                   false
% 31.64/4.49  --abstr_ref_sig_restrict                funpre
% 31.64/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.64/4.49  --abstr_ref_under                       []
% 31.64/4.49  
% 31.64/4.49  ------ SAT Options
% 31.64/4.49  
% 31.64/4.49  --sat_mode                              false
% 31.64/4.49  --sat_fm_restart_options                ""
% 31.64/4.49  --sat_gr_def                            false
% 31.64/4.49  --sat_epr_types                         true
% 31.64/4.49  --sat_non_cyclic_types                  false
% 31.64/4.49  --sat_finite_models                     false
% 31.64/4.49  --sat_fm_lemmas                         false
% 31.64/4.49  --sat_fm_prep                           false
% 31.64/4.49  --sat_fm_uc_incr                        true
% 31.64/4.49  --sat_out_model                         small
% 31.64/4.49  --sat_out_clauses                       false
% 31.64/4.49  
% 31.64/4.49  ------ QBF Options
% 31.64/4.49  
% 31.64/4.49  --qbf_mode                              false
% 31.64/4.49  --qbf_elim_univ                         false
% 31.64/4.49  --qbf_dom_inst                          none
% 31.64/4.49  --qbf_dom_pre_inst                      false
% 31.64/4.49  --qbf_sk_in                             false
% 31.64/4.49  --qbf_pred_elim                         true
% 31.64/4.49  --qbf_split                             512
% 31.64/4.49  
% 31.64/4.49  ------ BMC1 Options
% 31.64/4.49  
% 31.64/4.49  --bmc1_incremental                      false
% 31.64/4.49  --bmc1_axioms                           reachable_all
% 31.64/4.49  --bmc1_min_bound                        0
% 31.64/4.49  --bmc1_max_bound                        -1
% 31.64/4.49  --bmc1_max_bound_default                -1
% 31.64/4.49  --bmc1_symbol_reachability              true
% 31.64/4.49  --bmc1_property_lemmas                  false
% 31.64/4.49  --bmc1_k_induction                      false
% 31.64/4.49  --bmc1_non_equiv_states                 false
% 31.64/4.49  --bmc1_deadlock                         false
% 31.64/4.49  --bmc1_ucm                              false
% 31.64/4.49  --bmc1_add_unsat_core                   none
% 31.64/4.49  --bmc1_unsat_core_children              false
% 31.64/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.64/4.49  --bmc1_out_stat                         full
% 31.64/4.49  --bmc1_ground_init                      false
% 31.64/4.49  --bmc1_pre_inst_next_state              false
% 31.64/4.49  --bmc1_pre_inst_state                   false
% 31.64/4.49  --bmc1_pre_inst_reach_state             false
% 31.64/4.49  --bmc1_out_unsat_core                   false
% 31.64/4.49  --bmc1_aig_witness_out                  false
% 31.64/4.49  --bmc1_verbose                          false
% 31.64/4.49  --bmc1_dump_clauses_tptp                false
% 31.64/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.64/4.49  --bmc1_dump_file                        -
% 31.64/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.64/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.64/4.49  --bmc1_ucm_extend_mode                  1
% 31.64/4.49  --bmc1_ucm_init_mode                    2
% 31.64/4.49  --bmc1_ucm_cone_mode                    none
% 31.64/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.64/4.49  --bmc1_ucm_relax_model                  4
% 31.64/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.64/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.64/4.49  --bmc1_ucm_layered_model                none
% 31.64/4.49  --bmc1_ucm_max_lemma_size               10
% 31.64/4.49  
% 31.64/4.49  ------ AIG Options
% 31.64/4.49  
% 31.64/4.49  --aig_mode                              false
% 31.64/4.49  
% 31.64/4.49  ------ Instantiation Options
% 31.64/4.49  
% 31.64/4.49  --instantiation_flag                    true
% 31.64/4.49  --inst_sos_flag                         true
% 31.64/4.49  --inst_sos_phase                        true
% 31.64/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.64/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.64/4.49  --inst_lit_sel_side                     num_symb
% 31.64/4.49  --inst_solver_per_active                1400
% 31.64/4.49  --inst_solver_calls_frac                1.
% 31.64/4.49  --inst_passive_queue_type               priority_queues
% 31.64/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.64/4.49  --inst_passive_queues_freq              [25;2]
% 31.64/4.49  --inst_dismatching                      true
% 31.64/4.49  --inst_eager_unprocessed_to_passive     true
% 31.64/4.49  --inst_prop_sim_given                   true
% 31.64/4.49  --inst_prop_sim_new                     false
% 31.64/4.49  --inst_subs_new                         false
% 31.64/4.49  --inst_eq_res_simp                      false
% 31.64/4.49  --inst_subs_given                       false
% 31.64/4.49  --inst_orphan_elimination               true
% 31.64/4.49  --inst_learning_loop_flag               true
% 31.64/4.49  --inst_learning_start                   3000
% 31.64/4.49  --inst_learning_factor                  2
% 31.64/4.49  --inst_start_prop_sim_after_learn       3
% 31.64/4.49  --inst_sel_renew                        solver
% 31.64/4.49  --inst_lit_activity_flag                true
% 31.64/4.49  --inst_restr_to_given                   false
% 31.64/4.49  --inst_activity_threshold               500
% 31.64/4.49  --inst_out_proof                        true
% 31.64/4.49  
% 31.64/4.49  ------ Resolution Options
% 31.64/4.49  
% 31.64/4.49  --resolution_flag                       true
% 31.64/4.49  --res_lit_sel                           adaptive
% 31.64/4.49  --res_lit_sel_side                      none
% 31.64/4.49  --res_ordering                          kbo
% 31.64/4.49  --res_to_prop_solver                    active
% 31.64/4.49  --res_prop_simpl_new                    false
% 31.64/4.49  --res_prop_simpl_given                  true
% 31.64/4.49  --res_passive_queue_type                priority_queues
% 31.64/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.64/4.49  --res_passive_queues_freq               [15;5]
% 31.64/4.49  --res_forward_subs                      full
% 31.64/4.49  --res_backward_subs                     full
% 31.64/4.49  --res_forward_subs_resolution           true
% 31.64/4.49  --res_backward_subs_resolution          true
% 31.64/4.49  --res_orphan_elimination                true
% 31.64/4.49  --res_time_limit                        2.
% 31.64/4.49  --res_out_proof                         true
% 31.64/4.49  
% 31.64/4.49  ------ Superposition Options
% 31.64/4.49  
% 31.64/4.49  --superposition_flag                    true
% 31.64/4.49  --sup_passive_queue_type                priority_queues
% 31.64/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.64/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.64/4.49  --demod_completeness_check              fast
% 31.64/4.49  --demod_use_ground                      true
% 31.64/4.49  --sup_to_prop_solver                    passive
% 31.64/4.49  --sup_prop_simpl_new                    true
% 31.64/4.49  --sup_prop_simpl_given                  true
% 31.64/4.49  --sup_fun_splitting                     true
% 31.64/4.49  --sup_smt_interval                      50000
% 31.64/4.49  
% 31.64/4.49  ------ Superposition Simplification Setup
% 31.64/4.49  
% 31.64/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.64/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.64/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.64/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.64/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.64/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.64/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.64/4.49  --sup_immed_triv                        [TrivRules]
% 31.64/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.64/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.64/4.49  --sup_immed_bw_main                     []
% 31.64/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.64/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.64/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.64/4.49  --sup_input_bw                          []
% 31.64/4.49  
% 31.64/4.49  ------ Combination Options
% 31.64/4.49  
% 31.64/4.49  --comb_res_mult                         3
% 31.64/4.49  --comb_sup_mult                         2
% 31.64/4.49  --comb_inst_mult                        10
% 31.64/4.49  
% 31.64/4.49  ------ Debug Options
% 31.64/4.49  
% 31.64/4.49  --dbg_backtrace                         false
% 31.64/4.49  --dbg_dump_prop_clauses                 false
% 31.64/4.49  --dbg_dump_prop_clauses_file            -
% 31.64/4.49  --dbg_out_stat                          false
% 31.64/4.49  ------ Parsing...
% 31.64/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.64/4.49  
% 31.64/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 31.64/4.49  
% 31.64/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.64/4.49  
% 31.64/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.64/4.49  ------ Proving...
% 31.64/4.49  ------ Problem Properties 
% 31.64/4.49  
% 31.64/4.49  
% 31.64/4.49  clauses                                 34
% 31.64/4.49  conjectures                             1
% 31.64/4.49  EPR                                     1
% 31.64/4.49  Horn                                    26
% 31.64/4.49  unary                                   5
% 31.64/4.49  binary                                  6
% 31.64/4.49  lits                                    98
% 31.64/4.49  lits eq                                 20
% 31.64/4.49  fd_pure                                 0
% 31.64/4.49  fd_pseudo                               0
% 31.64/4.49  fd_cond                                 2
% 31.64/4.49  fd_pseudo_cond                          3
% 31.64/4.49  AC symbols                              0
% 31.64/4.49  
% 31.64/4.49  ------ Schedule dynamic 5 is on 
% 31.64/4.49  
% 31.64/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.64/4.49  
% 31.64/4.49  
% 31.64/4.49  ------ 
% 31.64/4.49  Current options:
% 31.64/4.49  ------ 
% 31.64/4.49  
% 31.64/4.49  ------ Input Options
% 31.64/4.49  
% 31.64/4.49  --out_options                           all
% 31.64/4.49  --tptp_safe_out                         true
% 31.64/4.49  --problem_path                          ""
% 31.64/4.49  --include_path                          ""
% 31.64/4.49  --clausifier                            res/vclausify_rel
% 31.64/4.49  --clausifier_options                    ""
% 31.64/4.49  --stdin                                 false
% 31.64/4.49  --stats_out                             all
% 31.64/4.49  
% 31.64/4.49  ------ General Options
% 31.64/4.49  
% 31.64/4.49  --fof                                   false
% 31.64/4.49  --time_out_real                         305.
% 31.64/4.49  --time_out_virtual                      -1.
% 31.64/4.49  --symbol_type_check                     false
% 31.64/4.49  --clausify_out                          false
% 31.64/4.49  --sig_cnt_out                           false
% 31.64/4.49  --trig_cnt_out                          false
% 31.64/4.49  --trig_cnt_out_tolerance                1.
% 31.64/4.49  --trig_cnt_out_sk_spl                   false
% 31.64/4.49  --abstr_cl_out                          false
% 31.64/4.49  
% 31.64/4.49  ------ Global Options
% 31.64/4.49  
% 31.64/4.49  --schedule                              default
% 31.64/4.49  --add_important_lit                     false
% 31.64/4.49  --prop_solver_per_cl                    1000
% 31.64/4.49  --min_unsat_core                        false
% 31.64/4.49  --soft_assumptions                      false
% 31.64/4.49  --soft_lemma_size                       3
% 31.64/4.49  --prop_impl_unit_size                   0
% 31.64/4.49  --prop_impl_unit                        []
% 31.64/4.49  --share_sel_clauses                     true
% 31.64/4.49  --reset_solvers                         false
% 31.64/4.49  --bc_imp_inh                            [conj_cone]
% 31.64/4.49  --conj_cone_tolerance                   3.
% 31.64/4.49  --extra_neg_conj                        none
% 31.64/4.49  --large_theory_mode                     true
% 31.64/4.49  --prolific_symb_bound                   200
% 31.64/4.49  --lt_threshold                          2000
% 31.64/4.49  --clause_weak_htbl                      true
% 31.64/4.49  --gc_record_bc_elim                     false
% 31.64/4.49  
% 31.64/4.49  ------ Preprocessing Options
% 31.64/4.49  
% 31.64/4.49  --preprocessing_flag                    true
% 31.64/4.49  --time_out_prep_mult                    0.1
% 31.64/4.49  --splitting_mode                        input
% 31.64/4.49  --splitting_grd                         true
% 31.64/4.49  --splitting_cvd                         false
% 31.64/4.49  --splitting_cvd_svl                     false
% 31.64/4.49  --splitting_nvd                         32
% 31.64/4.49  --sub_typing                            true
% 31.64/4.49  --prep_gs_sim                           true
% 31.64/4.49  --prep_unflatten                        true
% 31.64/4.49  --prep_res_sim                          true
% 31.64/4.49  --prep_upred                            true
% 31.64/4.49  --prep_sem_filter                       exhaustive
% 31.64/4.49  --prep_sem_filter_out                   false
% 31.64/4.49  --pred_elim                             true
% 31.64/4.49  --res_sim_input                         true
% 31.64/4.49  --eq_ax_congr_red                       true
% 31.64/4.49  --pure_diseq_elim                       true
% 31.64/4.49  --brand_transform                       false
% 31.64/4.49  --non_eq_to_eq                          false
% 31.64/4.49  --prep_def_merge                        true
% 31.64/4.49  --prep_def_merge_prop_impl              false
% 31.64/4.49  --prep_def_merge_mbd                    true
% 31.64/4.49  --prep_def_merge_tr_red                 false
% 31.64/4.49  --prep_def_merge_tr_cl                  false
% 31.64/4.49  --smt_preprocessing                     true
% 31.64/4.49  --smt_ac_axioms                         fast
% 31.64/4.49  --preprocessed_out                      false
% 31.64/4.49  --preprocessed_stats                    false
% 31.64/4.49  
% 31.64/4.49  ------ Abstraction refinement Options
% 31.64/4.49  
% 31.64/4.49  --abstr_ref                             []
% 31.64/4.49  --abstr_ref_prep                        false
% 31.64/4.49  --abstr_ref_until_sat                   false
% 31.64/4.49  --abstr_ref_sig_restrict                funpre
% 31.64/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.64/4.49  --abstr_ref_under                       []
% 31.64/4.49  
% 31.64/4.49  ------ SAT Options
% 31.64/4.49  
% 31.64/4.49  --sat_mode                              false
% 31.64/4.49  --sat_fm_restart_options                ""
% 31.64/4.49  --sat_gr_def                            false
% 31.64/4.49  --sat_epr_types                         true
% 31.64/4.49  --sat_non_cyclic_types                  false
% 31.64/4.49  --sat_finite_models                     false
% 31.64/4.49  --sat_fm_lemmas                         false
% 31.64/4.49  --sat_fm_prep                           false
% 31.64/4.49  --sat_fm_uc_incr                        true
% 31.64/4.49  --sat_out_model                         small
% 31.64/4.49  --sat_out_clauses                       false
% 31.64/4.49  
% 31.64/4.49  ------ QBF Options
% 31.64/4.49  
% 31.64/4.49  --qbf_mode                              false
% 31.64/4.49  --qbf_elim_univ                         false
% 31.64/4.49  --qbf_dom_inst                          none
% 31.64/4.49  --qbf_dom_pre_inst                      false
% 31.64/4.49  --qbf_sk_in                             false
% 31.64/4.49  --qbf_pred_elim                         true
% 31.64/4.49  --qbf_split                             512
% 31.64/4.49  
% 31.64/4.49  ------ BMC1 Options
% 31.64/4.49  
% 31.64/4.49  --bmc1_incremental                      false
% 31.64/4.49  --bmc1_axioms                           reachable_all
% 31.64/4.49  --bmc1_min_bound                        0
% 31.64/4.49  --bmc1_max_bound                        -1
% 31.64/4.49  --bmc1_max_bound_default                -1
% 31.64/4.49  --bmc1_symbol_reachability              true
% 31.64/4.49  --bmc1_property_lemmas                  false
% 31.64/4.49  --bmc1_k_induction                      false
% 31.64/4.49  --bmc1_non_equiv_states                 false
% 31.64/4.49  --bmc1_deadlock                         false
% 31.64/4.49  --bmc1_ucm                              false
% 31.64/4.49  --bmc1_add_unsat_core                   none
% 31.64/4.49  --bmc1_unsat_core_children              false
% 31.64/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.64/4.49  --bmc1_out_stat                         full
% 31.64/4.49  --bmc1_ground_init                      false
% 31.64/4.49  --bmc1_pre_inst_next_state              false
% 31.64/4.49  --bmc1_pre_inst_state                   false
% 31.64/4.49  --bmc1_pre_inst_reach_state             false
% 31.64/4.49  --bmc1_out_unsat_core                   false
% 31.64/4.49  --bmc1_aig_witness_out                  false
% 31.64/4.49  --bmc1_verbose                          false
% 31.64/4.49  --bmc1_dump_clauses_tptp                false
% 31.64/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.64/4.49  --bmc1_dump_file                        -
% 31.64/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.64/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.64/4.49  --bmc1_ucm_extend_mode                  1
% 31.64/4.49  --bmc1_ucm_init_mode                    2
% 31.64/4.49  --bmc1_ucm_cone_mode                    none
% 31.64/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.64/4.49  --bmc1_ucm_relax_model                  4
% 31.64/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.64/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.64/4.49  --bmc1_ucm_layered_model                none
% 31.64/4.49  --bmc1_ucm_max_lemma_size               10
% 31.64/4.49  
% 31.64/4.49  ------ AIG Options
% 31.64/4.49  
% 31.64/4.49  --aig_mode                              false
% 31.64/4.49  
% 31.64/4.49  ------ Instantiation Options
% 31.64/4.49  
% 31.64/4.49  --instantiation_flag                    true
% 31.64/4.49  --inst_sos_flag                         true
% 31.64/4.49  --inst_sos_phase                        true
% 31.64/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.64/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.64/4.49  --inst_lit_sel_side                     none
% 31.64/4.49  --inst_solver_per_active                1400
% 31.64/4.49  --inst_solver_calls_frac                1.
% 31.64/4.49  --inst_passive_queue_type               priority_queues
% 31.64/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.64/4.49  --inst_passive_queues_freq              [25;2]
% 31.64/4.49  --inst_dismatching                      true
% 31.64/4.49  --inst_eager_unprocessed_to_passive     true
% 31.64/4.49  --inst_prop_sim_given                   true
% 31.64/4.49  --inst_prop_sim_new                     false
% 31.64/4.49  --inst_subs_new                         false
% 31.64/4.49  --inst_eq_res_simp                      false
% 31.64/4.49  --inst_subs_given                       false
% 31.64/4.49  --inst_orphan_elimination               true
% 31.64/4.49  --inst_learning_loop_flag               true
% 31.64/4.49  --inst_learning_start                   3000
% 31.64/4.49  --inst_learning_factor                  2
% 31.64/4.49  --inst_start_prop_sim_after_learn       3
% 31.64/4.49  --inst_sel_renew                        solver
% 31.64/4.49  --inst_lit_activity_flag                true
% 31.64/4.49  --inst_restr_to_given                   false
% 31.64/4.49  --inst_activity_threshold               500
% 31.64/4.49  --inst_out_proof                        true
% 31.64/4.49  
% 31.64/4.49  ------ Resolution Options
% 31.64/4.49  
% 31.64/4.49  --resolution_flag                       false
% 31.64/4.49  --res_lit_sel                           adaptive
% 31.64/4.49  --res_lit_sel_side                      none
% 31.64/4.49  --res_ordering                          kbo
% 31.64/4.49  --res_to_prop_solver                    active
% 31.64/4.49  --res_prop_simpl_new                    false
% 31.64/4.49  --res_prop_simpl_given                  true
% 31.64/4.49  --res_passive_queue_type                priority_queues
% 31.64/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.64/4.49  --res_passive_queues_freq               [15;5]
% 31.64/4.49  --res_forward_subs                      full
% 31.64/4.49  --res_backward_subs                     full
% 31.64/4.49  --res_forward_subs_resolution           true
% 31.64/4.49  --res_backward_subs_resolution          true
% 31.64/4.49  --res_orphan_elimination                true
% 31.64/4.49  --res_time_limit                        2.
% 31.64/4.49  --res_out_proof                         true
% 31.64/4.49  
% 31.64/4.49  ------ Superposition Options
% 31.64/4.49  
% 31.64/4.49  --superposition_flag                    true
% 31.64/4.49  --sup_passive_queue_type                priority_queues
% 31.64/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.64/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.64/4.49  --demod_completeness_check              fast
% 31.64/4.49  --demod_use_ground                      true
% 31.64/4.49  --sup_to_prop_solver                    passive
% 31.64/4.49  --sup_prop_simpl_new                    true
% 31.64/4.49  --sup_prop_simpl_given                  true
% 31.64/4.49  --sup_fun_splitting                     true
% 31.64/4.49  --sup_smt_interval                      50000
% 31.64/4.49  
% 31.64/4.49  ------ Superposition Simplification Setup
% 31.64/4.49  
% 31.64/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.64/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.64/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.64/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.64/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.64/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.64/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.64/4.49  --sup_immed_triv                        [TrivRules]
% 31.64/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.64/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.64/4.49  --sup_immed_bw_main                     []
% 31.64/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.64/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.64/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.64/4.49  --sup_input_bw                          []
% 31.64/4.49  
% 31.64/4.49  ------ Combination Options
% 31.64/4.49  
% 31.64/4.49  --comb_res_mult                         3
% 31.64/4.49  --comb_sup_mult                         2
% 31.64/4.49  --comb_inst_mult                        10
% 31.64/4.49  
% 31.64/4.49  ------ Debug Options
% 31.64/4.49  
% 31.64/4.49  --dbg_backtrace                         false
% 31.64/4.49  --dbg_dump_prop_clauses                 false
% 31.64/4.49  --dbg_dump_prop_clauses_file            -
% 31.64/4.49  --dbg_out_stat                          false
% 31.64/4.49  
% 31.64/4.49  
% 31.64/4.49  
% 31.64/4.49  
% 31.64/4.49  ------ Proving...
% 31.64/4.49  
% 31.64/4.49  
% 31.64/4.49  % SZS status Theorem for theBenchmark.p
% 31.64/4.49  
% 31.64/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.64/4.49  
% 31.64/4.49  fof(f11,axiom,(
% 31.64/4.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f39,plain,(
% 31.64/4.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f11])).
% 31.64/4.49  
% 31.64/4.49  fof(f40,plain,(
% 31.64/4.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f39])).
% 31.64/4.49  
% 31.64/4.49  fof(f112,plain,(
% 31.64/4.49    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f40])).
% 31.64/4.49  
% 31.64/4.49  fof(f17,conjecture,(
% 31.64/4.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f18,negated_conjecture,(
% 31.64/4.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 31.64/4.49    inference(negated_conjecture,[],[f17])).
% 31.64/4.49  
% 31.64/4.49  fof(f51,plain,(
% 31.64/4.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f18])).
% 31.64/4.49  
% 31.64/4.49  fof(f52,plain,(
% 31.64/4.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f51])).
% 31.64/4.49  
% 31.64/4.49  fof(f83,plain,(
% 31.64/4.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) | ~l3_lattices(sK9) | ~v13_lattices(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9))),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f84,plain,(
% 31.64/4.49    (k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) | ~l3_lattices(sK9) | ~v13_lattices(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9)),
% 31.64/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f52,f83])).
% 31.64/4.49  
% 31.64/4.49  fof(f128,plain,(
% 31.64/4.49    ~v2_struct_0(sK9)),
% 31.64/4.49    inference(cnf_transformation,[],[f84])).
% 31.64/4.49  
% 31.64/4.49  fof(f131,plain,(
% 31.64/4.49    l3_lattices(sK9)),
% 31.64/4.49    inference(cnf_transformation,[],[f84])).
% 31.64/4.49  
% 31.64/4.49  fof(f6,axiom,(
% 31.64/4.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f19,plain,(
% 31.64/4.49    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 31.64/4.49    inference(pure_predicate_removal,[],[f6])).
% 31.64/4.49  
% 31.64/4.49  fof(f30,plain,(
% 31.64/4.49    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 31.64/4.49    inference(ennf_transformation,[],[f19])).
% 31.64/4.49  
% 31.64/4.49  fof(f96,plain,(
% 31.64/4.49    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f30])).
% 31.64/4.49  
% 31.64/4.49  fof(f8,axiom,(
% 31.64/4.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f33,plain,(
% 31.64/4.49    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f8])).
% 31.64/4.49  
% 31.64/4.49  fof(f34,plain,(
% 31.64/4.49    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f33])).
% 31.64/4.49  
% 31.64/4.49  fof(f58,plain,(
% 31.64/4.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(nnf_transformation,[],[f34])).
% 31.64/4.49  
% 31.64/4.49  fof(f59,plain,(
% 31.64/4.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(rectify,[],[f58])).
% 31.64/4.49  
% 31.64/4.49  fof(f61,plain,(
% 31.64/4.49    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f60,plain,(
% 31.64/4.49    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f62,plain,(
% 31.64/4.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f59,f61,f60])).
% 31.64/4.49  
% 31.64/4.49  fof(f102,plain,(
% 31.64/4.49    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f62])).
% 31.64/4.49  
% 31.64/4.49  fof(f15,axiom,(
% 31.64/4.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f47,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f15])).
% 31.64/4.49  
% 31.64/4.49  fof(f48,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f47])).
% 31.64/4.49  
% 31.64/4.49  fof(f123,plain,(
% 31.64/4.49    ( ! [X0,X1] : (k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f48])).
% 31.64/4.49  
% 31.64/4.49  fof(f130,plain,(
% 31.64/4.49    v4_lattice3(sK9)),
% 31.64/4.49    inference(cnf_transformation,[],[f84])).
% 31.64/4.49  
% 31.64/4.49  fof(f129,plain,(
% 31.64/4.49    v10_lattices(sK9)),
% 31.64/4.49    inference(cnf_transformation,[],[f84])).
% 31.64/4.49  
% 31.64/4.49  fof(f4,axiom,(
% 31.64/4.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f26,plain,(
% 31.64/4.49    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f4])).
% 31.64/4.49  
% 31.64/4.49  fof(f27,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f26])).
% 31.64/4.49  
% 31.64/4.49  fof(f53,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(nnf_transformation,[],[f27])).
% 31.64/4.49  
% 31.64/4.49  fof(f54,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(rectify,[],[f53])).
% 31.64/4.49  
% 31.64/4.49  fof(f55,plain,(
% 31.64/4.49    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f56,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).
% 31.64/4.49  
% 31.64/4.49  fof(f93,plain,(
% 31.64/4.49    ( ! [X0,X1] : (k5_lattices(X0) = X1 | m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f56])).
% 31.64/4.49  
% 31.64/4.49  fof(f5,axiom,(
% 31.64/4.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f28,plain,(
% 31.64/4.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f5])).
% 31.64/4.49  
% 31.64/4.49  fof(f29,plain,(
% 31.64/4.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f28])).
% 31.64/4.49  
% 31.64/4.49  fof(f95,plain,(
% 31.64/4.49    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f29])).
% 31.64/4.49  
% 31.64/4.49  fof(f10,axiom,(
% 31.64/4.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f37,plain,(
% 31.64/4.49    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f10])).
% 31.64/4.49  
% 31.64/4.49  fof(f38,plain,(
% 31.64/4.49    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f37])).
% 31.64/4.49  
% 31.64/4.49  fof(f67,plain,(
% 31.64/4.49    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(nnf_transformation,[],[f38])).
% 31.64/4.49  
% 31.64/4.49  fof(f68,plain,(
% 31.64/4.49    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(rectify,[],[f67])).
% 31.64/4.49  
% 31.64/4.49  fof(f70,plain,(
% 31.64/4.49    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK5(X0)) != k2_lattices(X0,sK5(X0),X1) & m1_subset_1(sK5(X0),u1_struct_0(X0))))) )),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f69,plain,(
% 31.64/4.49    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK4(X0)) != k2_lattices(X0,sK4(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f71,plain,(
% 31.64/4.49    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f68,f70,f69])).
% 31.64/4.49  
% 31.64/4.49  fof(f108,plain,(
% 31.64/4.49    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f71])).
% 31.64/4.49  
% 31.64/4.49  fof(f3,axiom,(
% 31.64/4.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f20,plain,(
% 31.64/4.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 31.64/4.49    inference(pure_predicate_removal,[],[f3])).
% 31.64/4.49  
% 31.64/4.49  fof(f21,plain,(
% 31.64/4.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 31.64/4.49    inference(pure_predicate_removal,[],[f20])).
% 31.64/4.49  
% 31.64/4.49  fof(f22,plain,(
% 31.64/4.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 31.64/4.49    inference(pure_predicate_removal,[],[f21])).
% 31.64/4.49  
% 31.64/4.49  fof(f24,plain,(
% 31.64/4.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 31.64/4.49    inference(ennf_transformation,[],[f22])).
% 31.64/4.49  
% 31.64/4.49  fof(f25,plain,(
% 31.64/4.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 31.64/4.49    inference(flattening,[],[f24])).
% 31.64/4.49  
% 31.64/4.49  fof(f88,plain,(
% 31.64/4.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f25])).
% 31.64/4.49  
% 31.64/4.49  fof(f132,plain,(
% 31.64/4.49    k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) | ~l3_lattices(sK9) | ~v13_lattices(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)),
% 31.64/4.49    inference(cnf_transformation,[],[f84])).
% 31.64/4.49  
% 31.64/4.49  fof(f92,plain,(
% 31.64/4.49    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f56])).
% 31.64/4.49  
% 31.64/4.49  fof(f133,plain,(
% 31.64/4.49    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(equality_resolution,[],[f92])).
% 31.64/4.49  
% 31.64/4.49  fof(f13,axiom,(
% 31.64/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f43,plain,(
% 31.64/4.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 31.64/4.49    inference(ennf_transformation,[],[f13])).
% 31.64/4.49  
% 31.64/4.49  fof(f44,plain,(
% 31.64/4.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.64/4.49    inference(flattening,[],[f43])).
% 31.64/4.49  
% 31.64/4.49  fof(f72,plain,(
% 31.64/4.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ! [X3] : (~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.64/4.49    inference(nnf_transformation,[],[f44])).
% 31.64/4.49  
% 31.64/4.49  fof(f73,plain,(
% 31.64/4.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ! [X3] : (~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattices(X1,X2,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.64/4.49    inference(rectify,[],[f72])).
% 31.64/4.49  
% 31.64/4.49  fof(f74,plain,(
% 31.64/4.49    ! [X2,X1,X0] : (? [X4] : (r3_lattices(X1,X2,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattices(X1,X2,sK6(X0,X1,X2)) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f75,plain,(
% 31.64/4.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ! [X3] : (~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattices(X1,X2,sK6(X0,X1,X2)) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.64/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f73,f74])).
% 31.64/4.49  
% 31.64/4.49  fof(f117,plain,(
% 31.64/4.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f75])).
% 31.64/4.49  
% 31.64/4.49  fof(f135,plain,(
% 31.64/4.49    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_4_lattice3(X1,X2)) | ~r3_lattices(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.64/4.49    inference(equality_resolution,[],[f117])).
% 31.64/4.49  
% 31.64/4.49  fof(f124,plain,(
% 31.64/4.49    ( ! [X0,X1] : (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f48])).
% 31.64/4.49  
% 31.64/4.49  fof(f14,axiom,(
% 31.64/4.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f45,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f14])).
% 31.64/4.49  
% 31.64/4.49  fof(f46,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f45])).
% 31.64/4.49  
% 31.64/4.49  fof(f76,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(nnf_transformation,[],[f46])).
% 31.64/4.49  
% 31.64/4.49  fof(f77,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f76])).
% 31.64/4.49  
% 31.64/4.49  fof(f78,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(rectify,[],[f77])).
% 31.64/4.49  
% 31.64/4.49  fof(f79,plain,(
% 31.64/4.49    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK7(X0,X1,X2),X1) & r3_lattice3(X0,sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f80,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK7(X0,X1,X2),X1) & r3_lattice3(X0,sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f78,f79])).
% 31.64/4.49  
% 31.64/4.49  fof(f118,plain,(
% 31.64/4.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f80])).
% 31.64/4.49  
% 31.64/4.49  fof(f137,plain,(
% 31.64/4.49    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(equality_resolution,[],[f118])).
% 31.64/4.49  
% 31.64/4.49  fof(f12,axiom,(
% 31.64/4.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f41,plain,(
% 31.64/4.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f12])).
% 31.64/4.49  
% 31.64/4.49  fof(f42,plain,(
% 31.64/4.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f41])).
% 31.64/4.49  
% 31.64/4.49  fof(f113,plain,(
% 31.64/4.49    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f42])).
% 31.64/4.49  
% 31.64/4.49  fof(f16,axiom,(
% 31.64/4.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f49,plain,(
% 31.64/4.49    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f16])).
% 31.64/4.49  
% 31.64/4.49  fof(f50,plain,(
% 31.64/4.49    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f49])).
% 31.64/4.49  
% 31.64/4.49  fof(f81,plain,(
% 31.64/4.49    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK8(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f82,plain,(
% 31.64/4.49    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK8(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f81])).
% 31.64/4.49  
% 31.64/4.49  fof(f126,plain,(
% 31.64/4.49    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | r2_hidden(sK8(X0,X1,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f82])).
% 31.64/4.49  
% 31.64/4.49  fof(f1,axiom,(
% 31.64/4.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f85,plain,(
% 31.64/4.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f1])).
% 31.64/4.49  
% 31.64/4.49  fof(f2,axiom,(
% 31.64/4.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f23,plain,(
% 31.64/4.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 31.64/4.49    inference(ennf_transformation,[],[f2])).
% 31.64/4.49  
% 31.64/4.49  fof(f86,plain,(
% 31.64/4.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f23])).
% 31.64/4.49  
% 31.64/4.49  fof(f9,axiom,(
% 31.64/4.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f35,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f9])).
% 31.64/4.49  
% 31.64/4.49  fof(f36,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f35])).
% 31.64/4.49  
% 31.64/4.49  fof(f63,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(nnf_transformation,[],[f36])).
% 31.64/4.49  
% 31.64/4.49  fof(f64,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(rectify,[],[f63])).
% 31.64/4.49  
% 31.64/4.49  fof(f65,plain,(
% 31.64/4.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 31.64/4.49    introduced(choice_axiom,[])).
% 31.64/4.49  
% 31.64/4.49  fof(f66,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f64,f65])).
% 31.64/4.49  
% 31.64/4.49  fof(f104,plain,(
% 31.64/4.49    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f66])).
% 31.64/4.49  
% 31.64/4.49  fof(f90,plain,(
% 31.64/4.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f25])).
% 31.64/4.49  
% 31.64/4.49  fof(f7,axiom,(
% 31.64/4.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 31.64/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.64/4.49  
% 31.64/4.49  fof(f31,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 31.64/4.49    inference(ennf_transformation,[],[f7])).
% 31.64/4.49  
% 31.64/4.49  fof(f32,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(flattening,[],[f31])).
% 31.64/4.49  
% 31.64/4.49  fof(f57,plain,(
% 31.64/4.49    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 31.64/4.49    inference(nnf_transformation,[],[f32])).
% 31.64/4.49  
% 31.64/4.49  fof(f97,plain,(
% 31.64/4.49    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f57])).
% 31.64/4.49  
% 31.64/4.49  fof(f89,plain,(
% 31.64/4.49    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f25])).
% 31.64/4.49  
% 31.64/4.49  fof(f103,plain,(
% 31.64/4.49    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 31.64/4.49    inference(cnf_transformation,[],[f62])).
% 31.64/4.49  
% 31.64/4.49  cnf(c_27,plain,
% 31.64/4.49      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f112]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_47,negated_conjecture,
% 31.64/4.49      ( ~ v2_struct_0(sK9) ),
% 31.64/4.49      inference(cnf_transformation,[],[f128]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1957,plain,
% 31.64/4.49      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | sK9 != X0 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_27,c_47]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1958,plain,
% 31.64/4.49      ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
% 31.64/4.49      | ~ l3_lattices(sK9) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1957]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_44,negated_conjecture,
% 31.64/4.49      ( l3_lattices(sK9) ),
% 31.64/4.49      inference(cnf_transformation,[],[f131]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1962,plain,
% 31.64/4.49      ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1958,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4147,plain,
% 31.64/4.49      ( m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_1962]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4804,plain,
% 31.64/4.49      ( m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) = iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4147]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_11,plain,
% 31.64/4.49      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f96]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_15,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 31.64/4.49      | ~ l1_lattices(X1)
% 31.64/4.49      | v13_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1) ),
% 31.64/4.49      inference(cnf_transformation,[],[f102]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1015,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 31.64/4.49      | v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X2)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | X1 != X2 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1016,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 31.64/4.49      | v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1015]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2131,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 31.64/4.49      | v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | sK9 != X1 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_1016,c_47]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2132,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | m1_subset_1(sK1(sK9,X0),u1_struct_0(sK9))
% 31.64/4.49      | v13_lattices(sK9)
% 31.64/4.49      | ~ l3_lattices(sK9) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_2131]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2136,plain,
% 31.64/4.49      ( v13_lattices(sK9)
% 31.64/4.49      | m1_subset_1(sK1(sK9,X0),u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_2132,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2137,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | m1_subset_1(sK1(sK9,X0),u1_struct_0(sK9))
% 31.64/4.49      | v13_lattices(sK9) ),
% 31.64/4.49      inference(renaming,[status(thm)],[c_2136]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4139,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | m1_subset_1(sK1(sK9,X0_62),u1_struct_0(sK9))
% 31.64/4.49      | v13_lattices(sK9) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_2137]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4812,plain,
% 31.64/4.49      ( m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(sK1(sK9,X0_62),u1_struct_0(sK9)) = iProver_top
% 31.64/4.49      | v13_lattices(sK9) = iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4139]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_39,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ v4_lattice3(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | ~ v10_lattices(X1)
% 31.64/4.49      | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0 ),
% 31.64/4.49      inference(cnf_transformation,[],[f123]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_45,negated_conjecture,
% 31.64/4.49      ( v4_lattice3(sK9) ),
% 31.64/4.49      inference(cnf_transformation,[],[f130]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1362,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | ~ v10_lattices(X1)
% 31.64/4.49      | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0
% 31.64/4.49      | sK9 != X1 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_39,c_45]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1363,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9)
% 31.64/4.49      | ~ v10_lattices(sK9)
% 31.64/4.49      | k15_lattice3(sK9,a_2_3_lattice3(sK9,X0)) = X0 ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1362]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_46,negated_conjecture,
% 31.64/4.49      ( v10_lattices(sK9) ),
% 31.64/4.49      inference(cnf_transformation,[],[f129]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1367,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | k15_lattice3(sK9,a_2_3_lattice3(sK9,X0)) = X0 ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1363,c_47,c_46,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4167,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | k15_lattice3(sK9,a_2_3_lattice3(sK9,X0_62)) = X0_62 ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_1367]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4784,plain,
% 31.64/4.49      ( k15_lattice3(sK9,a_2_3_lattice3(sK9,X0_62)) = X0_62
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4167]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_7251,plain,
% 31.64/4.49      ( k15_lattice3(sK9,a_2_3_lattice3(sK9,sK1(sK9,X0_62))) = sK1(sK9,X0_62)
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | v13_lattices(sK9) = iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4812,c_4784]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_10643,plain,
% 31.64/4.49      ( k15_lattice3(sK9,a_2_3_lattice3(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)))) = sK1(sK9,k15_lattice3(sK9,X0_63))
% 31.64/4.49      | v13_lattices(sK9) = iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4804,c_7251]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_7,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 31.64/4.49      | ~ l1_lattices(X1)
% 31.64/4.49      | ~ v13_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | k5_lattices(X1) = X0 ),
% 31.64/4.49      inference(cnf_transformation,[],[f93]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1110,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 31.64/4.49      | ~ v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X2)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | X1 != X2
% 31.64/4.49      | k5_lattices(X1) = X0 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_11,c_7]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1111,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 31.64/4.49      | ~ v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | k5_lattices(X1) = X0 ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1110]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2041,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 31.64/4.49      | ~ v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | k5_lattices(X1) = X0
% 31.64/4.49      | sK9 != X1 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_1111,c_47]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2042,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | m1_subset_1(sK0(sK9,X0),u1_struct_0(sK9))
% 31.64/4.49      | ~ v13_lattices(sK9)
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) = X0 ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_2041]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2046,plain,
% 31.64/4.49      ( ~ v13_lattices(sK9)
% 31.64/4.49      | m1_subset_1(sK0(sK9,X0),u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | k5_lattices(sK9) = X0 ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_2042,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2047,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | m1_subset_1(sK0(sK9,X0),u1_struct_0(sK9))
% 31.64/4.49      | ~ v13_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) = X0 ),
% 31.64/4.49      inference(renaming,[status(thm)],[c_2046]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4143,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | m1_subset_1(sK0(sK9,X0_62),u1_struct_0(sK9))
% 31.64/4.49      | ~ v13_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) = X0_62 ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_2047]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4808,plain,
% 31.64/4.49      ( k5_lattices(sK9) = X0_62
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(sK0(sK9,X0_62),u1_struct_0(sK9)) = iProver_top
% 31.64/4.49      | v13_lattices(sK9) != iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4143]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_10,plain,
% 31.64/4.49      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 31.64/4.49      | ~ l1_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f95]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_935,plain,
% 31.64/4.49      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0) ),
% 31.64/4.49      inference(resolution,[status(thm)],[c_11,c_10]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1891,plain,
% 31.64/4.49      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | sK9 != X0 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_935,c_47]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1892,plain,
% 31.64/4.49      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 31.64/4.49      | ~ l3_lattices(sK9) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1891]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_147,plain,
% 31.64/4.49      ( l1_lattices(sK9) | ~ l3_lattices(sK9) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_11]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_150,plain,
% 31.64/4.49      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 31.64/4.49      | ~ l1_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_10]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1894,plain,
% 31.64/4.49      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1892,c_47,c_44,c_147,c_150]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4151,plain,
% 31.64/4.49      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_1894]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4800,plain,
% 31.64/4.49      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) = iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4151]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_26,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.64/4.49      | ~ l1_lattices(X1)
% 31.64/4.49      | ~ v6_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 31.64/4.49      inference(cnf_transformation,[],[f108]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_949,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.64/4.49      | ~ v6_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X3)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | X1 != X3
% 31.64/4.49      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_950,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.64/4.49      | ~ v6_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_949]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2194,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.64/4.49      | ~ v6_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 31.64/4.49      | sK9 != X1 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_950,c_47]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2195,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 31.64/4.49      | ~ v6_lattices(sK9)
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_2194]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4,plain,
% 31.64/4.49      ( v6_lattices(X0)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f88]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1760,plain,
% 31.64/4.49      ( v6_lattices(X0)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | sK9 != X0 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_4,c_46]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1761,plain,
% 31.64/4.49      ( v6_lattices(sK9) | ~ l3_lattices(sK9) | v2_struct_0(sK9) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1760]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_166,plain,
% 31.64/4.49      ( v6_lattices(sK9)
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9)
% 31.64/4.49      | ~ v10_lattices(sK9) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1763,plain,
% 31.64/4.49      ( v6_lattices(sK9) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1761,c_47,c_46,c_44,c_166]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1849,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 31.64/4.49      | sK9 != X1 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_950,c_1763]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1850,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9)
% 31.64/4.49      | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1849]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1854,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 31.64/4.49      | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1850,c_47,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2198,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 31.64/4.49      | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_2195,c_47,c_44,c_1850]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4152,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X1_62,u1_struct_0(sK9))
% 31.64/4.49      | k2_lattices(sK9,X0_62,X1_62) = k2_lattices(sK9,X1_62,X0_62) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_2198]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4799,plain,
% 31.64/4.49      ( k2_lattices(sK9,X0_62,X1_62) = k2_lattices(sK9,X1_62,X0_62)
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4152]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5654,plain,
% 31.64/4.49      ( k2_lattices(sK9,X0_62,k5_lattices(sK9)) = k2_lattices(sK9,k5_lattices(sK9),X0_62)
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4800,c_4799]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_9341,plain,
% 31.64/4.49      ( k2_lattices(sK9,sK0(sK9,X0_62),k5_lattices(sK9)) = k2_lattices(sK9,k5_lattices(sK9),sK0(sK9,X0_62))
% 31.64/4.49      | k5_lattices(sK9) = X0_62
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | v13_lattices(sK9) != iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4808,c_5654]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_76056,plain,
% 31.64/4.49      ( k2_lattices(sK9,k5_lattices(sK9),sK0(sK9,k15_lattice3(sK9,X0_63))) = k2_lattices(sK9,sK0(sK9,k15_lattice3(sK9,X0_63)),k5_lattices(sK9))
% 31.64/4.49      | k15_lattice3(sK9,X0_63) = k5_lattices(sK9)
% 31.64/4.49      | v13_lattices(sK9) != iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4804,c_9341]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4178,plain,
% 31.64/4.49      ( X0_63 != X1_63
% 31.64/4.49      | k15_lattice3(X0_61,X0_63) = k15_lattice3(X0_61,X1_63) ),
% 31.64/4.49      theory(equality) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4185,plain,
% 31.64/4.49      ( k1_xboole_0 != k1_xboole_0
% 31.64/4.49      | k15_lattice3(sK9,k1_xboole_0) = k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4178]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4172,plain,( X0_63 = X0_63 ),theory(equality) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4190,plain,
% 31.64/4.49      ( k1_xboole_0 = k1_xboole_0 ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4172]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_43,negated_conjecture,
% 31.64/4.49      ( ~ v13_lattices(sK9)
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9)
% 31.64/4.49      | ~ v10_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f132]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_281,negated_conjecture,
% 31.64/4.49      ( ~ v13_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_43,c_47,c_46,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4169,negated_conjecture,
% 31.64/4.49      ( ~ v13_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_281]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4191,plain,
% 31.64/4.49      ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
% 31.64/4.49      | v13_lattices(sK9) != iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4169]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4246,plain,
% 31.64/4.49      ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4147]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4245,plain,
% 31.64/4.49      ( m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) = iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4147]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4247,plain,
% 31.64/4.49      ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) = iProver_top ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4245]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_8,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 31.64/4.49      | ~ l1_lattices(X1)
% 31.64/4.49      | ~ v13_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
% 31.64/4.49      inference(cnf_transformation,[],[f133]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1085,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 31.64/4.49      | ~ v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X2)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | X1 != X2
% 31.64/4.49      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_11,c_8]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1086,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 31.64/4.49      | ~ v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1085]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1096,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
% 31.64/4.49      inference(forward_subsumption_resolution,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1086,c_935]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2065,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ v13_lattices(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1)
% 31.64/4.49      | sK9 != X1 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_1096,c_47]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2066,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ v13_lattices(sK9)
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | k2_lattices(sK9,X0,k5_lattices(sK9)) = k5_lattices(sK9) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_2065]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2070,plain,
% 31.64/4.49      ( ~ v13_lattices(sK9)
% 31.64/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | k2_lattices(sK9,X0,k5_lattices(sK9)) = k5_lattices(sK9) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_2066,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2071,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ v13_lattices(sK9)
% 31.64/4.49      | k2_lattices(sK9,X0,k5_lattices(sK9)) = k5_lattices(sK9) ),
% 31.64/4.49      inference(renaming,[status(thm)],[c_2070]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4142,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | ~ v13_lattices(sK9)
% 31.64/4.49      | k2_lattices(sK9,X0_62,k5_lattices(sK9)) = k5_lattices(sK9) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_2071]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5335,plain,
% 31.64/4.49      ( ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
% 31.64/4.49      | ~ v13_lattices(sK9)
% 31.64/4.49      | k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) = k5_lattices(sK9) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4142]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5336,plain,
% 31.64/4.49      ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) = k5_lattices(sK9)
% 31.64/4.49      | m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | v13_lattices(sK9) != iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_5335]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5338,plain,
% 31.64/4.49      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) = k5_lattices(sK9)
% 31.64/4.49      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | v13_lattices(sK9) != iProver_top ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_5336]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4173,plain,
% 31.64/4.49      ( X0_62 != X1_62 | X2_62 != X1_62 | X2_62 = X0_62 ),
% 31.64/4.49      theory(equality) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5188,plain,
% 31.64/4.49      ( k15_lattice3(sK9,k1_xboole_0) != X0_62
% 31.64/4.49      | k5_lattices(sK9) != X0_62
% 31.64/4.49      | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4173]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5551,plain,
% 31.64/4.49      ( k15_lattice3(sK9,k1_xboole_0) != k5_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0)
% 31.64/4.49      | k5_lattices(sK9) != k5_lattices(sK9) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_5188]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_29,plain,
% 31.64/4.49      ( ~ r3_lattices(X0,X1,X2)
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | r2_hidden(X2,a_2_4_lattice3(X0,X1))
% 31.64/4.49      | ~ v4_lattice3(X0)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f135]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1632,plain,
% 31.64/4.49      ( ~ r3_lattices(X0,X1,X2)
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.64/4.49      | r2_hidden(X2,a_2_4_lattice3(X0,X1))
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0)
% 31.64/4.49      | sK9 != X0 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_29,c_45]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1633,plain,
% 31.64/4.49      ( ~ r3_lattices(sK9,X0,X1)
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | r2_hidden(X1,a_2_4_lattice3(sK9,X0))
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9)
% 31.64/4.49      | ~ v10_lattices(sK9) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1632]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1637,plain,
% 31.64/4.49      ( r2_hidden(X1,a_2_4_lattice3(sK9,X0))
% 31.64/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 31.64/4.49      | ~ r3_lattices(sK9,X0,X1) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1633,c_47,c_46,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1638,plain,
% 31.64/4.49      ( ~ r3_lattices(sK9,X0,X1)
% 31.64/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 31.64/4.49      | r2_hidden(X1,a_2_4_lattice3(sK9,X0)) ),
% 31.64/4.49      inference(renaming,[status(thm)],[c_1637]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4155,plain,
% 31.64/4.49      ( ~ r3_lattices(sK9,X0_62,X1_62)
% 31.64/4.49      | ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X1_62,u1_struct_0(sK9))
% 31.64/4.49      | r2_hidden(X1_62,a_2_4_lattice3(sK9,X0_62)) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_1638]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4980,plain,
% 31.64/4.49      ( ~ r3_lattices(sK9,k15_lattice3(sK9,X0_63),X0_62)
% 31.64/4.49      | ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
% 31.64/4.49      | r2_hidden(X0_62,a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4155]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_6294,plain,
% 31.64/4.49      ( ~ r3_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9))
% 31.64/4.49      | ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 31.64/4.49      | r2_hidden(k5_lattices(sK9),a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4980]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_6296,plain,
% 31.64/4.49      ( ~ r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9))
% 31.64/4.49      | ~ m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 31.64/4.49      | r2_hidden(k5_lattices(sK9),a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0))) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_6294]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_38,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ v4_lattice3(X1)
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | ~ v10_lattices(X1)
% 31.64/4.49      | k16_lattice3(X1,a_2_4_lattice3(X1,X0)) = X0 ),
% 31.64/4.49      inference(cnf_transformation,[],[f124]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1380,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.49      | ~ l3_lattices(X1)
% 31.64/4.49      | v2_struct_0(X1)
% 31.64/4.49      | ~ v10_lattices(X1)
% 31.64/4.49      | k16_lattice3(X1,a_2_4_lattice3(X1,X0)) = X0
% 31.64/4.49      | sK9 != X1 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_38,c_45]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1381,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9)
% 31.64/4.49      | ~ v10_lattices(sK9)
% 31.64/4.49      | k16_lattice3(sK9,a_2_4_lattice3(sK9,X0)) = X0 ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1380]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1385,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | k16_lattice3(sK9,a_2_4_lattice3(sK9,X0)) = X0 ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1381,c_47,c_46,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4166,plain,
% 31.64/4.49      ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)) = X0_62 ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_1385]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4785,plain,
% 31.64/4.49      ( k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)) = X0_62
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4166]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5326,plain,
% 31.64/4.49      ( k16_lattice3(sK9,a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) = k15_lattice3(sK9,X0_63) ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4804,c_4785]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_37,plain,
% 31.64/4.49      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 31.64/4.49      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 31.64/4.49      | ~ v4_lattice3(X0)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f137]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_28,plain,
% 31.64/4.49      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f113]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_291,plain,
% 31.64/4.49      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 31.64/4.49      | ~ v4_lattice3(X0)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_37,c_28]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1440,plain,
% 31.64/4.49      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0)
% 31.64/4.49      | sK9 != X0 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_291,c_45]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1441,plain,
% 31.64/4.49      ( r3_lattice3(sK9,k16_lattice3(sK9,X0),X0)
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9)
% 31.64/4.49      | ~ v10_lattices(sK9) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1440]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1445,plain,
% 31.64/4.49      ( r3_lattice3(sK9,k16_lattice3(sK9,X0),X0) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1441,c_47,c_46,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4163,plain,
% 31.64/4.49      ( r3_lattice3(sK9,k16_lattice3(sK9,X0_63),X0_63) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_1445]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4788,plain,
% 31.64/4.49      ( r3_lattice3(sK9,k16_lattice3(sK9,X0_63),X0_63) = iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4163]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_6382,plain,
% 31.64/4.49      ( r3_lattice3(sK9,k15_lattice3(sK9,X0_63),a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) = iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_5326,c_4788]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_6385,plain,
% 31.64/4.49      ( r3_lattice3(sK9,k15_lattice3(sK9,X0_63),a_2_4_lattice3(sK9,k15_lattice3(sK9,X0_63))) ),
% 31.64/4.49      inference(predicate_to_equality_rev,[status(thm)],[c_6382]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_6387,plain,
% 31.64/4.49      ( r3_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0),a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0))) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_6385]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4171,plain,( X0_62 = X0_62 ),theory(equality) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_6586,plain,
% 31.64/4.49      ( k5_lattices(sK9) = k5_lattices(sK9) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4171]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5317,plain,
% 31.64/4.49      ( k15_lattice3(sK9,a_2_3_lattice3(sK9,k5_lattices(sK9))) = k5_lattices(sK9) ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4800,c_4784]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_41,plain,
% 31.64/4.49      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 31.64/4.49      | r2_hidden(sK8(X0,X1,X2),X1)
% 31.64/4.49      | ~ v4_lattice3(X0)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f126]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1473,plain,
% 31.64/4.49      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 31.64/4.49      | r2_hidden(sK8(X0,X1,X2),X1)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0)
% 31.64/4.49      | sK9 != X0 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_41,c_45]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1474,plain,
% 31.64/4.49      ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1))
% 31.64/4.49      | r2_hidden(sK8(sK9,X0,X1),X0)
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9)
% 31.64/4.49      | ~ v10_lattices(sK9) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1473]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1478,plain,
% 31.64/4.49      ( r2_hidden(sK8(sK9,X0,X1),X0)
% 31.64/4.49      | r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1)) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1474,c_47,c_46,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1479,plain,
% 31.64/4.49      ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1))
% 31.64/4.49      | r2_hidden(sK8(sK9,X0,X1),X0) ),
% 31.64/4.49      inference(renaming,[status(thm)],[c_1478]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4161,plain,
% 31.64/4.49      ( r3_lattices(sK9,k15_lattice3(sK9,X0_63),k15_lattice3(sK9,X1_63))
% 31.64/4.49      | r2_hidden(sK8(sK9,X0_63,X1_63),X0_63) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_1479]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4790,plain,
% 31.64/4.49      ( r3_lattices(sK9,k15_lattice3(sK9,X0_63),k15_lattice3(sK9,X1_63)) = iProver_top
% 31.64/4.49      | r2_hidden(sK8(sK9,X0_63,X1_63),X0_63) = iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4161]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_0,plain,
% 31.64/4.49      ( r1_tarski(k1_xboole_0,X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f85]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1,plain,
% 31.64/4.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f86]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_542,plain,
% 31.64/4.49      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_543,plain,
% 31.64/4.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_542]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4168,plain,
% 31.64/4.49      ( ~ r2_hidden(X0_62,k1_xboole_0) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_543]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4783,plain,
% 31.64/4.49      ( r2_hidden(X0_62,k1_xboole_0) != iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4168]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_7218,plain,
% 31.64/4.49      ( r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0_63)) = iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4790,c_4783]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_7429,plain,
% 31.64/4.49      ( r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) = iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_5317,c_7218]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_7432,plain,
% 31.64/4.49      ( r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) ),
% 31.64/4.49      inference(predicate_to_equality_rev,[status(thm)],[c_7429]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5552,plain,
% 31.64/4.49      ( X0_62 != X1_62
% 31.64/4.49      | k5_lattices(sK9) != X1_62
% 31.64/4.49      | k5_lattices(sK9) = X0_62 ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4173]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_7048,plain,
% 31.64/4.49      ( X0_62 != k5_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) = X0_62
% 31.64/4.49      | k5_lattices(sK9) != k5_lattices(sK9) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_5552]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_9016,plain,
% 31.64/4.49      ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) != k5_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) = k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9))
% 31.64/4.49      | k5_lattices(sK9) != k5_lattices(sK9) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_7048]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_9022,plain,
% 31.64/4.49      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) != k5_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) = k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9))
% 31.64/4.49      | k5_lattices(sK9) != k5_lattices(sK9) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_9016]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_22,plain,
% 31.64/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.64/4.49      | r1_lattices(X0,X1,X3)
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.64/4.49      | ~ r2_hidden(X3,X2)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f104]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_2,plain,
% 31.64/4.49      ( ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0)
% 31.64/4.49      | v9_lattices(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f90]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_13,plain,
% 31.64/4.49      ( ~ r1_lattices(X0,X1,X2)
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.64/4.49      | ~ v8_lattices(X0)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v9_lattices(X0)
% 31.64/4.49      | k2_lattices(X0,X1,X2) = X1 ),
% 31.64/4.49      inference(cnf_transformation,[],[f97]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_553,plain,
% 31.64/4.49      ( ~ r1_lattices(X0,X1,X2)
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.64/4.49      | ~ v8_lattices(X0)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0)
% 31.64/4.49      | k2_lattices(X0,X1,X2) = X1 ),
% 31.64/4.49      inference(resolution,[status(thm)],[c_2,c_13]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_3,plain,
% 31.64/4.49      ( v8_lattices(X0)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0) ),
% 31.64/4.49      inference(cnf_transformation,[],[f89]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_557,plain,
% 31.64/4.49      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | ~ r1_lattices(X0,X1,X2)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0)
% 31.64/4.49      | k2_lattices(X0,X1,X2) = X1 ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_553,c_3]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_558,plain,
% 31.64/4.49      ( ~ r1_lattices(X0,X1,X2)
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0)
% 31.64/4.49      | k2_lattices(X0,X1,X2) = X1 ),
% 31.64/4.49      inference(renaming,[status(thm)],[c_557]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_759,plain,
% 31.64/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 31.64/4.49      | ~ m1_subset_1(X6,u1_struct_0(X5))
% 31.64/4.49      | ~ r2_hidden(X3,X2)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | ~ l3_lattices(X5)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | v2_struct_0(X5)
% 31.64/4.49      | ~ v10_lattices(X5)
% 31.64/4.49      | X6 != X3
% 31.64/4.49      | X4 != X1
% 31.64/4.49      | X5 != X0
% 31.64/4.49      | k2_lattices(X5,X4,X6) = X4 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_22,c_558]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_760,plain,
% 31.64/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.64/4.49      | ~ r2_hidden(X3,X2)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | ~ v10_lattices(X0)
% 31.64/4.49      | k2_lattices(X0,X1,X3) = X1 ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_759]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1733,plain,
% 31.64/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.64/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.64/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.64/4.49      | ~ r2_hidden(X3,X2)
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | v2_struct_0(X0)
% 31.64/4.49      | k2_lattices(X0,X1,X3) = X1
% 31.64/4.49      | sK9 != X0 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_760,c_46]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1734,plain,
% 31.64/4.49      ( ~ r3_lattice3(sK9,X0,X1)
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ r2_hidden(X2,X1)
% 31.64/4.49      | ~ l3_lattices(sK9)
% 31.64/4.49      | v2_struct_0(sK9)
% 31.64/4.49      | k2_lattices(sK9,X0,X2) = X0 ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1733]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1738,plain,
% 31.64/4.49      ( ~ r3_lattice3(sK9,X0,X1)
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ r2_hidden(X2,X1)
% 31.64/4.49      | k2_lattices(sK9,X0,X2) = X0 ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1734,c_47,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1739,plain,
% 31.64/4.49      ( ~ r3_lattice3(sK9,X0,X1)
% 31.64/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X2,u1_struct_0(sK9))
% 31.64/4.49      | ~ r2_hidden(X2,X1)
% 31.64/4.49      | k2_lattices(sK9,X0,X2) = X0 ),
% 31.64/4.49      inference(renaming,[status(thm)],[c_1738]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4153,plain,
% 31.64/4.49      ( ~ r3_lattice3(sK9,X0_62,X0_63)
% 31.64/4.49      | ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(X1_62,u1_struct_0(sK9))
% 31.64/4.49      | ~ r2_hidden(X1_62,X0_63)
% 31.64/4.49      | k2_lattices(sK9,X0_62,X1_62) = X0_62 ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_1739]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_5181,plain,
% 31.64/4.49      ( ~ r3_lattice3(sK9,k15_lattice3(sK9,X0_63),X1_63)
% 31.64/4.49      | ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
% 31.64/4.49      | ~ r2_hidden(X0_62,X1_63)
% 31.64/4.49      | k2_lattices(sK9,k15_lattice3(sK9,X0_63),X0_62) = k15_lattice3(sK9,X0_63) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4153]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_13757,plain,
% 31.64/4.49      ( ~ r3_lattice3(sK9,k15_lattice3(sK9,X0_63),a_2_4_lattice3(sK9,k15_lattice3(sK9,X1_63)))
% 31.64/4.49      | ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 31.64/4.49      | ~ r2_hidden(k5_lattices(sK9),a_2_4_lattice3(sK9,k15_lattice3(sK9,X1_63)))
% 31.64/4.49      | k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) = k15_lattice3(sK9,X0_63) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_5181]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_13759,plain,
% 31.64/4.49      ( ~ r3_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0),a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0)))
% 31.64/4.49      | ~ m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9))
% 31.64/4.49      | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 31.64/4.49      | ~ r2_hidden(k5_lattices(sK9),a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0)))
% 31.64/4.49      | k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) = k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_13757]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_11613,plain,
% 31.64/4.49      ( X0_62 != X1_62
% 31.64/4.49      | k15_lattice3(sK9,X0_63) != X1_62
% 31.64/4.49      | k15_lattice3(sK9,X0_63) = X0_62 ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4173]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_21345,plain,
% 31.64/4.49      ( X0_62 != k15_lattice3(sK9,X0_63)
% 31.64/4.49      | k15_lattice3(sK9,X1_63) = X0_62
% 31.64/4.49      | k15_lattice3(sK9,X1_63) != k15_lattice3(sK9,X0_63) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_11613]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_46425,plain,
% 31.64/4.49      ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) != k15_lattice3(sK9,X0_63)
% 31.64/4.49      | k15_lattice3(sK9,X1_63) = k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9))
% 31.64/4.49      | k15_lattice3(sK9,X1_63) != k15_lattice3(sK9,X0_63) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_21345]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_46426,plain,
% 31.64/4.49      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) != k15_lattice3(sK9,k1_xboole_0)
% 31.64/4.49      | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9))
% 31.64/4.49      | k15_lattice3(sK9,k1_xboole_0) != k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_46425]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_7200,plain,
% 31.64/4.49      ( X0_62 != X1_62
% 31.64/4.49      | X0_62 = k5_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) != X1_62 ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_4173]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_41390,plain,
% 31.64/4.49      ( k15_lattice3(sK9,k1_xboole_0) != X0_62
% 31.64/4.49      | k15_lattice3(sK9,k1_xboole_0) = k5_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) != X0_62 ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_7200]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_76491,plain,
% 31.64/4.49      ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9))
% 31.64/4.49      | k15_lattice3(sK9,k1_xboole_0) = k5_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) != k2_lattices(sK9,k15_lattice3(sK9,X0_63),k5_lattices(sK9)) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_41390]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_76492,plain,
% 31.64/4.49      ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9))
% 31.64/4.49      | k15_lattice3(sK9,k1_xboole_0) = k5_lattices(sK9)
% 31.64/4.49      | k5_lattices(sK9) != k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) ),
% 31.64/4.49      inference(instantiation,[status(thm)],[c_76491]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_76563,plain,
% 31.64/4.49      ( v13_lattices(sK9) != iProver_top ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_76056,c_47,c_44,c_147,c_150,c_4185,c_4190,c_4191,
% 31.64/4.49                 c_4246,c_4247,c_5338,c_5551,c_6296,c_6387,c_6586,c_7432,
% 31.64/4.49                 c_9022,c_13759,c_46426,c_76492]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_76571,plain,
% 31.64/4.49      ( k15_lattice3(sK9,a_2_3_lattice3(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)))) = sK1(sK9,k15_lattice3(sK9,X0_63)) ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_10643,c_76563]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1942,plain,
% 31.64/4.49      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 31.64/4.49      | ~ l3_lattices(X0)
% 31.64/4.49      | sK9 != X0 ),
% 31.64/4.49      inference(resolution_lifted,[status(thm)],[c_28,c_47]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1943,plain,
% 31.64/4.49      ( m1_subset_1(k16_lattice3(sK9,X0),u1_struct_0(sK9))
% 31.64/4.49      | ~ l3_lattices(sK9) ),
% 31.64/4.49      inference(unflattening,[status(thm)],[c_1942]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_1947,plain,
% 31.64/4.49      ( m1_subset_1(k16_lattice3(sK9,X0),u1_struct_0(sK9)) ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_1943,c_44]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4148,plain,
% 31.64/4.49      ( m1_subset_1(k16_lattice3(sK9,X0_63),u1_struct_0(sK9)) ),
% 31.64/4.49      inference(subtyping,[status(esa)],[c_1947]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4803,plain,
% 31.64/4.49      ( m1_subset_1(k16_lattice3(sK9,X0_63),u1_struct_0(sK9)) = iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4148]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4796,plain,
% 31.64/4.49      ( r3_lattices(sK9,X0_62,X1_62) != iProver_top
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | r2_hidden(X1_62,a_2_4_lattice3(sK9,X0_62)) = iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4155]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_4798,plain,
% 31.64/4.49      ( k2_lattices(sK9,X0_62,X1_62) = X0_62
% 31.64/4.49      | r3_lattice3(sK9,X0_62,X0_63) != iProver_top
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | r2_hidden(X1_62,X0_63) != iProver_top ),
% 31.64/4.49      inference(predicate_to_equality,[status(thm)],[c_4153]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_7029,plain,
% 31.64/4.49      ( k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = X0_62
% 31.64/4.49      | r3_lattice3(sK9,X0_62,X1_63) != iProver_top
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | r2_hidden(k15_lattice3(sK9,X0_63),X1_63) != iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4804,c_4798]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_9775,plain,
% 31.64/4.49      ( k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = X0_62
% 31.64/4.49      | r3_lattices(sK9,X1_62,k15_lattice3(sK9,X0_63)) != iProver_top
% 31.64/4.49      | r3_lattice3(sK9,X0_62,a_2_4_lattice3(sK9,X1_62)) != iProver_top
% 31.64/4.49      | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4796,c_7029]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_22885,plain,
% 31.64/4.49      ( m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | r3_lattice3(sK9,X0_62,a_2_4_lattice3(sK9,X1_62)) != iProver_top
% 31.64/4.49      | r3_lattices(sK9,X1_62,k15_lattice3(sK9,X0_63)) != iProver_top
% 31.64/4.49      | k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = X0_62 ),
% 31.64/4.49      inference(global_propositional_subsumption,
% 31.64/4.49                [status(thm)],
% 31.64/4.49                [c_9775,c_4245]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_22886,plain,
% 31.64/4.49      ( k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = X0_62
% 31.64/4.49      | r3_lattices(sK9,X1_62,k15_lattice3(sK9,X0_63)) != iProver_top
% 31.64/4.49      | r3_lattice3(sK9,X0_62,a_2_4_lattice3(sK9,X1_62)) != iProver_top
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.49      inference(renaming,[status(thm)],[c_22885]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_22892,plain,
% 31.64/4.49      ( k2_lattices(sK9,k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)),k15_lattice3(sK9,X0_63)) = k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62))
% 31.64/4.49      | r3_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) != iProver_top
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 31.64/4.49      | m1_subset_1(k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)),u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4788,c_22886]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_22946,plain,
% 31.64/4.49      ( k2_lattices(sK9,k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62)),k15_lattice3(sK9,X0_63)) = k16_lattice3(sK9,a_2_4_lattice3(sK9,X0_62))
% 31.64/4.49      | r3_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) != iProver_top
% 31.64/4.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.49      inference(superposition,[status(thm)],[c_4803,c_22892]) ).
% 31.64/4.49  
% 31.64/4.49  cnf(c_22963,plain,
% 31.64/4.49      ( k2_lattices(sK9,k16_lattice3(sK9,a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0))),k15_lattice3(sK9,X0_63)) = k16_lattice3(sK9,a_2_4_lattice3(sK9,k15_lattice3(sK9,k1_xboole_0)))
% 31.64/4.49      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.50      inference(superposition,[status(thm)],[c_7218,c_22946]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_22979,plain,
% 31.64/4.50      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0_63)) = k15_lattice3(sK9,k1_xboole_0)
% 31.64/4.50      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.50      inference(demodulation,[status(thm)],[c_22963,c_5326]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_44639,plain,
% 31.64/4.50      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0_63)) = k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.50      inference(global_propositional_subsumption,
% 31.64/4.50                [status(thm)],
% 31.64/4.50                [c_22979,c_4247]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_90394,plain,
% 31.64/4.50      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,X0_63))) = k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.50      inference(superposition,[status(thm)],[c_76571,c_44639]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_90518,plain,
% 31.64/4.50      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) = k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.50      inference(instantiation,[status(thm)],[c_90394]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_5655,plain,
% 31.64/4.50      ( k2_lattices(sK9,X0_62,k15_lattice3(sK9,X0_63)) = k2_lattices(sK9,k15_lattice3(sK9,X0_63),X0_62)
% 31.64/4.50      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top ),
% 31.64/4.50      inference(superposition,[status(thm)],[c_4804,c_4799]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_9396,plain,
% 31.64/4.50      ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k15_lattice3(sK9,X1_63)) = k2_lattices(sK9,k15_lattice3(sK9,X1_63),k15_lattice3(sK9,X0_63)) ),
% 31.64/4.50      inference(superposition,[status(thm)],[c_4804,c_5655]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_44647,plain,
% 31.64/4.50      ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.50      inference(superposition,[status(thm)],[c_44639,c_9396]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_90393,plain,
% 31.64/4.50      ( k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.50      inference(superposition,[status(thm)],[c_76571,c_44647]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_90517,plain,
% 31.64/4.50      ( k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
% 31.64/4.50      inference(instantiation,[status(thm)],[c_90393]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_14,plain,
% 31.64/4.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.50      | ~ l1_lattices(X1)
% 31.64/4.50      | v13_lattices(X1)
% 31.64/4.50      | v2_struct_0(X1)
% 31.64/4.50      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 31.64/4.50      | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
% 31.64/4.50      inference(cnf_transformation,[],[f103]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_1036,plain,
% 31.64/4.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.50      | v13_lattices(X1)
% 31.64/4.50      | ~ l3_lattices(X2)
% 31.64/4.50      | v2_struct_0(X1)
% 31.64/4.50      | X1 != X2
% 31.64/4.50      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 31.64/4.50      | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
% 31.64/4.50      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_1037,plain,
% 31.64/4.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.50      | v13_lattices(X1)
% 31.64/4.50      | ~ l3_lattices(X1)
% 31.64/4.50      | v2_struct_0(X1)
% 31.64/4.50      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 31.64/4.50      | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
% 31.64/4.50      inference(unflattening,[status(thm)],[c_1036]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_2107,plain,
% 31.64/4.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.64/4.50      | v13_lattices(X1)
% 31.64/4.50      | ~ l3_lattices(X1)
% 31.64/4.50      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 31.64/4.50      | k2_lattices(X1,sK1(X1,X0),X0) != X0
% 31.64/4.50      | sK9 != X1 ),
% 31.64/4.50      inference(resolution_lifted,[status(thm)],[c_1037,c_47]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_2108,plain,
% 31.64/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.50      | v13_lattices(sK9)
% 31.64/4.50      | ~ l3_lattices(sK9)
% 31.64/4.50      | k2_lattices(sK9,X0,sK1(sK9,X0)) != X0
% 31.64/4.50      | k2_lattices(sK9,sK1(sK9,X0),X0) != X0 ),
% 31.64/4.50      inference(unflattening,[status(thm)],[c_2107]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_2112,plain,
% 31.64/4.50      ( v13_lattices(sK9)
% 31.64/4.50      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.50      | k2_lattices(sK9,X0,sK1(sK9,X0)) != X0
% 31.64/4.50      | k2_lattices(sK9,sK1(sK9,X0),X0) != X0 ),
% 31.64/4.50      inference(global_propositional_subsumption,
% 31.64/4.50                [status(thm)],
% 31.64/4.50                [c_2108,c_44]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_2113,plain,
% 31.64/4.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 31.64/4.50      | v13_lattices(sK9)
% 31.64/4.50      | k2_lattices(sK9,X0,sK1(sK9,X0)) != X0
% 31.64/4.50      | k2_lattices(sK9,sK1(sK9,X0),X0) != X0 ),
% 31.64/4.50      inference(renaming,[status(thm)],[c_2112]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_4140,plain,
% 31.64/4.50      ( ~ m1_subset_1(X0_62,u1_struct_0(sK9))
% 31.64/4.50      | v13_lattices(sK9)
% 31.64/4.50      | k2_lattices(sK9,X0_62,sK1(sK9,X0_62)) != X0_62
% 31.64/4.50      | k2_lattices(sK9,sK1(sK9,X0_62),X0_62) != X0_62 ),
% 31.64/4.50      inference(subtyping,[status(esa)],[c_2113]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_5026,plain,
% 31.64/4.50      ( ~ m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9))
% 31.64/4.50      | v13_lattices(sK9)
% 31.64/4.50      | k2_lattices(sK9,k15_lattice3(sK9,X0_63),sK1(sK9,k15_lattice3(sK9,X0_63))) != k15_lattice3(sK9,X0_63)
% 31.64/4.50      | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)),k15_lattice3(sK9,X0_63)) != k15_lattice3(sK9,X0_63) ),
% 31.64/4.50      inference(instantiation,[status(thm)],[c_4140]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_5027,plain,
% 31.64/4.50      ( k2_lattices(sK9,k15_lattice3(sK9,X0_63),sK1(sK9,k15_lattice3(sK9,X0_63))) != k15_lattice3(sK9,X0_63)
% 31.64/4.50      | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,X0_63)),k15_lattice3(sK9,X0_63)) != k15_lattice3(sK9,X0_63)
% 31.64/4.50      | m1_subset_1(k15_lattice3(sK9,X0_63),u1_struct_0(sK9)) != iProver_top
% 31.64/4.50      | v13_lattices(sK9) = iProver_top ),
% 31.64/4.50      inference(predicate_to_equality,[status(thm)],[c_5026]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(c_5029,plain,
% 31.64/4.50      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK1(sK9,k15_lattice3(sK9,k1_xboole_0))) != k15_lattice3(sK9,k1_xboole_0)
% 31.64/4.50      | k2_lattices(sK9,sK1(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) != k15_lattice3(sK9,k1_xboole_0)
% 31.64/4.50      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 31.64/4.50      | v13_lattices(sK9) = iProver_top ),
% 31.64/4.50      inference(instantiation,[status(thm)],[c_5027]) ).
% 31.64/4.50  
% 31.64/4.50  cnf(contradiction,plain,
% 31.64/4.50      ( $false ),
% 31.64/4.50      inference(minisat,
% 31.64/4.50                [status(thm)],
% 31.64/4.50                [c_90518,c_90517,c_76563,c_5029,c_4247]) ).
% 31.64/4.50  
% 31.64/4.50  
% 31.64/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.64/4.50  
% 31.64/4.50  ------                               Statistics
% 31.64/4.50  
% 31.64/4.50  ------ General
% 31.64/4.50  
% 31.64/4.50  abstr_ref_over_cycles:                  0
% 31.64/4.50  abstr_ref_under_cycles:                 0
% 31.64/4.50  gc_basic_clause_elim:                   0
% 31.64/4.50  forced_gc_time:                         0
% 31.64/4.50  parsing_time:                           0.011
% 31.64/4.50  unif_index_cands_time:                  0.
% 31.64/4.50  unif_index_add_time:                    0.
% 31.64/4.50  orderings_time:                         0.
% 31.64/4.50  out_proof_time:                         0.03
% 31.64/4.50  total_time:                             3.553
% 31.64/4.50  num_of_symbols:                         65
% 31.64/4.50  num_of_terms:                           96581
% 31.64/4.50  
% 31.64/4.50  ------ Preprocessing
% 31.64/4.50  
% 31.64/4.50  num_of_splits:                          0
% 31.64/4.50  num_of_split_atoms:                     0
% 31.64/4.50  num_of_reused_defs:                     0
% 31.64/4.50  num_eq_ax_congr_red:                    80
% 31.64/4.50  num_of_sem_filtered_clauses:            1
% 31.64/4.50  num_of_subtypes:                        4
% 31.64/4.50  monotx_restored_types:                  1
% 31.64/4.50  sat_num_of_epr_types:                   0
% 31.64/4.50  sat_num_of_non_cyclic_types:            0
% 31.64/4.50  sat_guarded_non_collapsed_types:        1
% 31.64/4.50  num_pure_diseq_elim:                    0
% 31.64/4.50  simp_replaced_by:                       0
% 31.64/4.50  res_preprocessed:                       170
% 31.64/4.50  prep_upred:                             0
% 31.64/4.50  prep_unflattend:                        134
% 31.64/4.50  smt_new_axioms:                         0
% 31.64/4.50  pred_elim_cands:                        5
% 31.64/4.50  pred_elim:                              10
% 31.64/4.50  pred_elim_cl:                           13
% 31.64/4.50  pred_elim_cycles:                       17
% 31.64/4.50  merged_defs:                            0
% 31.64/4.50  merged_defs_ncl:                        0
% 31.64/4.50  bin_hyper_res:                          0
% 31.64/4.50  prep_cycles:                            4
% 31.64/4.50  pred_elim_time:                         0.06
% 31.64/4.50  splitting_time:                         0.
% 31.64/4.50  sem_filter_time:                        0.
% 31.64/4.50  monotx_time:                            0.
% 31.64/4.50  subtype_inf_time:                       0.001
% 31.64/4.50  
% 31.64/4.50  ------ Problem properties
% 31.64/4.50  
% 31.64/4.50  clauses:                                34
% 31.64/4.50  conjectures:                            1
% 31.64/4.50  epr:                                    1
% 31.64/4.50  horn:                                   26
% 31.64/4.50  ground:                                 3
% 31.64/4.50  unary:                                  5
% 31.64/4.50  binary:                                 6
% 31.64/4.50  lits:                                   98
% 31.64/4.50  lits_eq:                                20
% 31.64/4.50  fd_pure:                                0
% 31.64/4.50  fd_pseudo:                              0
% 31.64/4.50  fd_cond:                                2
% 31.64/4.50  fd_pseudo_cond:                         3
% 31.64/4.50  ac_symbols:                             0
% 31.64/4.50  
% 31.64/4.50  ------ Propositional Solver
% 31.64/4.50  
% 31.64/4.50  prop_solver_calls:                      52
% 31.64/4.50  prop_fast_solver_calls:                 4599
% 31.64/4.50  smt_solver_calls:                       0
% 31.64/4.50  smt_fast_solver_calls:                  0
% 31.64/4.50  prop_num_of_clauses:                    51841
% 31.64/4.50  prop_preprocess_simplified:             56290
% 31.64/4.50  prop_fo_subsumed:                       170
% 31.64/4.50  prop_solver_time:                       0.
% 31.64/4.50  smt_solver_time:                        0.
% 31.64/4.50  smt_fast_solver_time:                   0.
% 31.64/4.50  prop_fast_solver_time:                  0.
% 31.64/4.50  prop_unsat_core_time:                   0.004
% 31.64/4.50  
% 31.64/4.50  ------ QBF
% 31.64/4.50  
% 31.64/4.50  qbf_q_res:                              0
% 31.64/4.50  qbf_num_tautologies:                    0
% 31.64/4.50  qbf_prep_cycles:                        0
% 31.64/4.50  
% 31.64/4.50  ------ BMC1
% 31.64/4.50  
% 31.64/4.50  bmc1_current_bound:                     -1
% 31.64/4.50  bmc1_last_solved_bound:                 -1
% 31.64/4.50  bmc1_unsat_core_size:                   -1
% 31.64/4.50  bmc1_unsat_core_parents_size:           -1
% 31.64/4.50  bmc1_merge_next_fun:                    0
% 31.64/4.50  bmc1_unsat_core_clauses_time:           0.
% 31.64/4.50  
% 31.64/4.50  ------ Instantiation
% 31.64/4.50  
% 31.64/4.50  inst_num_of_clauses:                    1299
% 31.64/4.50  inst_num_in_passive:                    208
% 31.64/4.50  inst_num_in_active:                     2676
% 31.64/4.50  inst_num_in_unprocessed:                646
% 31.64/4.50  inst_num_of_loops:                      3479
% 31.64/4.50  inst_num_of_learning_restarts:          1
% 31.64/4.50  inst_num_moves_active_passive:          799
% 31.64/4.50  inst_lit_activity:                      0
% 31.64/4.50  inst_lit_activity_moves:                2
% 31.64/4.50  inst_num_tautologies:                   0
% 31.64/4.50  inst_num_prop_implied:                  0
% 31.64/4.50  inst_num_existing_simplified:           0
% 31.64/4.50  inst_num_eq_res_simplified:             0
% 31.64/4.50  inst_num_child_elim:                    0
% 31.64/4.50  inst_num_of_dismatching_blockings:      6720
% 31.64/4.50  inst_num_of_non_proper_insts:           7944
% 31.64/4.50  inst_num_of_duplicates:                 0
% 31.64/4.50  inst_inst_num_from_inst_to_res:         0
% 31.64/4.50  inst_dismatching_checking_time:         0.
% 31.64/4.50  
% 31.64/4.50  ------ Resolution
% 31.64/4.50  
% 31.64/4.50  res_num_of_clauses:                     44
% 31.64/4.50  res_num_in_passive:                     44
% 31.64/4.50  res_num_in_active:                      0
% 31.64/4.50  res_num_of_loops:                       174
% 31.64/4.50  res_forward_subset_subsumed:            177
% 31.64/4.50  res_backward_subset_subsumed:           0
% 31.64/4.50  res_forward_subsumed:                   0
% 31.64/4.50  res_backward_subsumed:                  0
% 31.64/4.50  res_forward_subsumption_resolution:     8
% 31.64/4.50  res_backward_subsumption_resolution:    1
% 31.64/4.50  res_clause_to_clause_subsumption:       38402
% 31.64/4.50  res_orphan_elimination:                 0
% 31.64/4.50  res_tautology_del:                      344
% 31.64/4.50  res_num_eq_res_simplified:              0
% 31.64/4.50  res_num_sel_changes:                    0
% 31.64/4.50  res_moves_from_active_to_pass:          0
% 31.64/4.50  
% 31.64/4.50  ------ Superposition
% 31.64/4.50  
% 31.64/4.50  sup_time_total:                         0.
% 31.64/4.50  sup_time_generating:                    0.
% 31.64/4.50  sup_time_sim_full:                      0.
% 31.64/4.50  sup_time_sim_immed:                     0.
% 31.64/4.50  
% 31.64/4.50  sup_num_of_clauses:                     6785
% 31.64/4.50  sup_num_in_active:                      358
% 31.64/4.50  sup_num_in_passive:                     6427
% 31.64/4.50  sup_num_of_loops:                       694
% 31.64/4.50  sup_fw_superposition:                   6104
% 31.64/4.50  sup_bw_superposition:                   3544
% 31.64/4.50  sup_immediate_simplified:               2207
% 31.64/4.50  sup_given_eliminated:                   92
% 31.64/4.50  comparisons_done:                       0
% 31.64/4.50  comparisons_avoided:                    94
% 31.64/4.50  
% 31.64/4.50  ------ Simplifications
% 31.64/4.50  
% 31.64/4.50  
% 31.64/4.50  sim_fw_subset_subsumed:                 163
% 31.64/4.50  sim_bw_subset_subsumed:                 174
% 31.64/4.50  sim_fw_subsumed:                        942
% 31.64/4.50  sim_bw_subsumed:                        330
% 31.64/4.50  sim_fw_subsumption_res:                 0
% 31.64/4.50  sim_bw_subsumption_res:                 0
% 31.64/4.50  sim_tautology_del:                      34
% 31.64/4.50  sim_eq_tautology_del:                   457
% 31.64/4.50  sim_eq_res_simp:                        0
% 31.64/4.50  sim_fw_demodulated:                     542
% 31.64/4.50  sim_bw_demodulated:                     2
% 31.64/4.50  sim_light_normalised:                   1283
% 31.64/4.50  sim_joinable_taut:                      0
% 31.64/4.50  sim_joinable_simp:                      0
% 31.64/4.50  sim_ac_normalised:                      0
% 31.64/4.50  sim_smt_subsumption:                    0
% 31.64/4.50  
%------------------------------------------------------------------------------
