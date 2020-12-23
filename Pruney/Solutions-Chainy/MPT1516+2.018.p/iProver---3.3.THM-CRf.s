%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:19 EST 2020

% Result     : Theorem 11.81s
% Output     : CNFRefutation 11.81s
% Verified   : 
% Statistics : Number of formulae       :  246 (2134 expanded)
%              Number of clauses        :  152 ( 582 expanded)
%              Number of leaves         :   27 ( 436 expanded)
%              Depth                    :   27
%              Number of atoms          : 1258 (14820 expanded)
%              Number of equality atoms :  295 (2042 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f19])).

fof(f75,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f66,plain,
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
   => ( ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
        | ~ l3_lattices(sK7)
        | ~ v13_lattices(sK7)
        | ~ v10_lattices(sK7)
        | v2_struct_0(sK7) )
      & l3_lattices(sK7)
      & v4_lattice3(sK7)
      & v10_lattices(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
      | ~ l3_lattices(sK7)
      | ~ v13_lattices(sK7)
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) )
    & l3_lattices(sK7)
    & v4_lattice3(sK7)
    & v10_lattices(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f66])).

fof(f104,plain,(
    v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f67])).

fof(f103,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f67])).

fof(f106,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f67])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK6(X0)) != k2_lattices(X0,sK6(X0),X1)
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,X2,sK5(X0)) != k2_lattices(X0,sK5(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f62,f64,f63])).

fof(f98,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f50,plain,(
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

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
        & r4_lattice3(X0,sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
                & r4_lattice3(X0,sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f105,plain,(
    v4_lattice3(sK7) ),
    inference(cnf_transformation,[],[f67])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK3(X0,X1,X2),X1)
                  & r2_hidden(sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f40])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f108,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f70])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X4,X0] :
      ( k2_lattices(X0,X4,sK2(X0)) = sK2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f107,plain,
    ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
    | ~ l3_lattices(sK7)
    | ~ v13_lattices(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f67])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2787,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2786,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4628,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_2787,c_2786])).

cnf(c_4,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_494,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_15])).

cnf(c_5,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_lattices(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_5])).

cnf(c_499,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(renaming,[status(thm)],[c_498])).

cnf(c_38,negated_conjecture,
    ( v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_856,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_499,c_38])).

cnf(c_857,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_856])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_36,negated_conjecture,
    ( l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_861,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_857,c_39,c_36])).

cnf(c_862,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_861])).

cnf(c_6897,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | X0 = k2_lattices(sK7,X0,X1) ),
    inference(resolution,[status(thm)],[c_4628,c_862])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1427,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_39])).

cnf(c_1428,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_lattices(sK7)
    | ~ v6_lattices(sK7)
    | k2_lattices(sK7,X0,X1) = k2_lattices(sK7,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1427])).

cnf(c_13,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_109,plain,
    ( l1_lattices(sK7)
    | ~ l3_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_880,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_38])).

cnf(c_881,plain,
    ( v6_lattices(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_128,plain,
    ( v6_lattices(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ v10_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_883,plain,
    ( v6_lattices(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_39,c_38,c_36,c_128])).

cnf(c_1152,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_883])).

cnf(c_1153,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l1_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,X0,X1) = k2_lattices(sK7,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1152])).

cnf(c_1431,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,X1) = k2_lattices(sK7,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1428,c_39,c_36,c_109,c_1153])).

cnf(c_1432,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X1,X0) = k2_lattices(sK7,X0,X1) ),
    inference(renaming,[status(thm)],[c_1431])).

cnf(c_4635,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | X2 != k2_lattices(sK7,X1,X0)
    | k2_lattices(sK7,X0,X1) = X2 ),
    inference(resolution,[status(thm)],[c_2787,c_1432])).

cnf(c_7173,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k2_lattices(sK7,X1,X0) = X0 ),
    inference(resolution,[status(thm)],[c_6897,c_4635])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1508,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_39])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l1_lattices(sK7)
    | v13_lattices(sK7)
    | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0
    | k2_lattices(sK7,sK1(sK7,X0),X0) != X0 ),
    inference(unflattening,[status(thm)],[c_1508])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v13_lattices(sK7)
    | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0
    | k2_lattices(sK7,sK1(sK7,X0),X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1509,c_36,c_109])).

cnf(c_8026,plain,
    ( ~ r1_lattices(sK7,X0,sK1(sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
    | v13_lattices(sK7)
    | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0 ),
    inference(resolution,[status(thm)],[c_7173,c_1513])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1487,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_1488,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
    | ~ l1_lattices(sK7)
    | v13_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1487])).

cnf(c_1492,plain,
    ( m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v13_lattices(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1488,c_36,c_109])).

cnf(c_1493,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
    | v13_lattices(sK7) ),
    inference(renaming,[status(thm)],[c_1492])).

cnf(c_8225,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_lattices(sK7,X0,sK1(sK7,X0))
    | v13_lattices(sK7)
    | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8026,c_1493])).

cnf(c_8226,plain,
    ( ~ r1_lattices(sK7,X0,sK1(sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v13_lattices(sK7)
    | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0 ),
    inference(renaming,[status(thm)],[c_8225])).

cnf(c_8688,plain,
    ( ~ r1_lattices(sK7,X0,sK1(sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
    | v13_lattices(sK7) ),
    inference(resolution,[status(thm)],[c_8226,c_862])).

cnf(c_8702,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_lattices(sK7,X0,sK1(sK7,X0))
    | v13_lattices(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8688,c_1493])).

cnf(c_8703,plain,
    ( ~ r1_lattices(sK7,X0,sK1(sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v13_lattices(sK7) ),
    inference(renaming,[status(thm)],[c_8702])).

cnf(c_34,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_903,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_36])).

cnf(c_904,plain,
    ( m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_908,plain,
    ( m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_904,c_39])).

cnf(c_28,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_37,negated_conjecture,
    ( v4_lattice3(sK7) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_714,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_715,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,k15_lattice3(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ v10_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_719,plain,
    ( ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r1_lattices(sK7,k15_lattice3(sK7,X1),X0)
    | ~ r4_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_715,c_39,c_38,c_36])).

cnf(c_720,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,k15_lattice3(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_719])).

cnf(c_1016,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,k15_lattice3(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_908,c_720])).

cnf(c_8928,plain,
    ( ~ r4_lattice3(sK7,sK1(sK7,k15_lattice3(sK7,X0)),X0)
    | ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK7,k15_lattice3(sK7,X0)),u1_struct_0(sK7))
    | v13_lattices(sK7) ),
    inference(resolution,[status(thm)],[c_8703,c_1016])).

cnf(c_3366,plain,
    ( ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
    | m1_subset_1(sK1(sK7,k15_lattice3(sK7,X0)),u1_struct_0(sK7))
    | v13_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_1493])).

cnf(c_27,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_738,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_739,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ v10_lattices(sK7)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_738])).

cnf(c_743,plain,
    ( m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r4_lattice3(sK7,X0,X1)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_39,c_38,c_36])).

cnf(c_744,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
    | k15_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_743])).

cnf(c_3290,plain,
    ( k15_lattice3(sK7,X0) = X1
    | r4_lattice3(sK7,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_22,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_966,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_967,plain,
    ( r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(sK3(sK7,X0,X1),X1)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_966])).

cnf(c_971,plain,
    ( r2_hidden(sK3(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r4_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_967,c_39])).

cnf(c_972,plain,
    ( r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(sK3(sK7,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_971])).

cnf(c_3282,plain,
    ( r4_lattice3(sK7,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK3(sK7,X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_972])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3293,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3472,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3293])).

cnf(c_4982,plain,
    ( r4_lattice3(sK7,X0,k1_xboole_0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_3472])).

cnf(c_7245,plain,
    ( k15_lattice3(sK7,X0) = X1
    | r4_lattice3(sK7,X1,X0) != iProver_top
    | r4_lattice3(sK7,sK4(sK7,X0,X1),k1_xboole_0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3290,c_4982])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1466,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,X0,sK2(X1)) = sK2(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_1467,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l1_lattices(sK7)
    | ~ v13_lattices(sK7)
    | k2_lattices(sK7,X0,sK2(sK7)) = sK2(sK7) ),
    inference(unflattening,[status(thm)],[c_1466])).

cnf(c_1471,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v13_lattices(sK7)
    | k2_lattices(sK7,X0,sK2(sK7)) = sK2(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1467,c_36,c_109])).

cnf(c_3275,plain,
    ( k2_lattices(sK7,X0,sK2(sK7)) = sK2(sK7)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v13_lattices(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1471])).

cnf(c_7250,plain,
    ( k2_lattices(sK7,sK4(sK7,X0,X1),sK2(sK7)) = sK2(sK7)
    | k15_lattice3(sK7,X0) = X1
    | r4_lattice3(sK7,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v13_lattices(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3290,c_3275])).

cnf(c_27703,plain,
    ( sK4(sK7,X0,X1) = k15_lattice3(sK7,k1_xboole_0)
    | k2_lattices(sK7,sK4(sK7,k1_xboole_0,sK4(sK7,X0,X1)),sK2(sK7)) = sK2(sK7)
    | k15_lattice3(sK7,X0) = X1
    | r4_lattice3(sK7,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,X0,X1),u1_struct_0(sK7)) != iProver_top
    | v13_lattices(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7245,c_7250])).

cnf(c_12,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_112,plain,
    ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | ~ l1_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_35,negated_conjecture,
    ( ~ v13_lattices(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ v10_lattices(sK7)
    | k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_221,negated_conjecture,
    ( ~ v13_lattices(sK7)
    | k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35,c_39,c_38,c_36])).

cnf(c_223,plain,
    ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
    | v13_lattices(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_2790,plain,
    ( X0 != X1
    | k5_lattices(X0) = k5_lattices(X1) ),
    theory(equality)).

cnf(c_2805,plain,
    ( k5_lattices(sK7) = k5_lattices(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2790])).

cnf(c_2819,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2786])).

cnf(c_3575,plain,
    ( k15_lattice3(sK7,k1_xboole_0) != X0
    | k5_lattices(sK7) != X0
    | k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2787])).

cnf(c_3705,plain,
    ( k15_lattice3(sK7,k1_xboole_0) != k5_lattices(sK7)
    | k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0)
    | k5_lattices(sK7) != k5_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_3575])).

cnf(c_1416,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_39])).

cnf(c_1417,plain,
    ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | ~ l1_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1416])).

cnf(c_1419,plain,
    ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1417,c_39,c_36,c_109,c_112])).

cnf(c_3277,plain,
    ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1419])).

cnf(c_5164,plain,
    ( r4_lattice3(sK7,k5_lattices(sK7),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3277,c_4982])).

cnf(c_5170,plain,
    ( r4_lattice3(sK7,k5_lattices(sK7),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5164])).

cnf(c_3911,plain,
    ( ~ r4_lattice3(sK7,k5_lattices(sK7),X0)
    | m1_subset_1(sK4(sK7,X0,k5_lattices(sK7)),u1_struct_0(sK7))
    | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | k15_lattice3(sK7,X0) = k5_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_7404,plain,
    ( ~ r4_lattice3(sK7,k5_lattices(sK7),k1_xboole_0)
    | m1_subset_1(sK4(sK7,k1_xboole_0,k5_lattices(sK7)),u1_struct_0(sK7))
    | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | k15_lattice3(sK7,k1_xboole_0) = k5_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_3911])).

cnf(c_14,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_526,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(resolution,[status(thm)],[c_4,c_14])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_lattices(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_5])).

cnf(c_531,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(renaming,[status(thm)],[c_530])).

cnf(c_832,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_531,c_38])).

cnf(c_833,plain,
    ( r1_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_832])).

cnf(c_837,plain,
    ( r1_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_833,c_39,c_36])).

cnf(c_838,plain,
    ( r1_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_837])).

cnf(c_3411,plain,
    ( r1_lattices(sK7,k5_lattices(sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | k2_lattices(sK7,k5_lattices(sK7),X0) != k5_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_22722,plain,
    ( r1_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7)))
    | ~ m1_subset_1(sK4(sK7,k1_xboole_0,k5_lattices(sK7)),u1_struct_0(sK7))
    | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | k2_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7))) != k5_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_3411])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1532,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_39])).

cnf(c_1533,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | ~ l1_lattices(sK7)
    | ~ v13_lattices(sK7)
    | k2_lattices(sK7,k5_lattices(sK7),X0) = k5_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1532])).

cnf(c_1537,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v13_lattices(sK7)
    | k2_lattices(sK7,k5_lattices(sK7),X0) = k5_lattices(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1533,c_39,c_36,c_109,c_112])).

cnf(c_3272,plain,
    ( k2_lattices(sK7,k5_lattices(sK7),X0) = k5_lattices(sK7)
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v13_lattices(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1537])).

cnf(c_7251,plain,
    ( k2_lattices(sK7,k5_lattices(sK7),sK4(sK7,X0,X1)) = k5_lattices(sK7)
    | k15_lattice3(sK7,X0) = X1
    | r4_lattice3(sK7,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v13_lattices(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3290,c_3272])).

cnf(c_28449,plain,
    ( k2_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7))) = k5_lattices(sK7)
    | k15_lattice3(sK7,k1_xboole_0) = k5_lattices(sK7)
    | m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) != iProver_top
    | v13_lattices(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5164,c_7251])).

cnf(c_40,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_43,plain,
    ( l3_lattices(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_108,plain,
    ( l1_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_110,plain,
    ( l1_lattices(sK7) = iProver_top
    | l3_lattices(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_111,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) = iProver_top
    | l1_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_113,plain,
    ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) = iProver_top
    | l1_lattices(sK7) != iProver_top
    | v2_struct_0(sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_28749,plain,
    ( k2_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7))) = k5_lattices(sK7)
    | v13_lattices(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28449,c_40,c_43,c_110,c_113,c_223,c_2805,c_2819,c_3705])).

cnf(c_25,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_786,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_787,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ v10_lattices(sK7)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
    | ~ r4_lattice3(sK7,X0,X1)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_39,c_38,c_36])).

cnf(c_792,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k15_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_791])).

cnf(c_30590,plain,
    ( ~ r4_lattice3(sK7,k5_lattices(sK7),k1_xboole_0)
    | ~ r1_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7)))
    | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | k15_lattice3(sK7,k1_xboole_0) = k5_lattices(sK7) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_30684,plain,
    ( v13_lattices(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27703,c_39,c_36,c_109,c_112,c_223,c_2805,c_2819,c_3705,c_5170,c_7404,c_22722,c_28749,c_30590])).

cnf(c_30686,plain,
    ( ~ v13_lattices(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_30684])).

cnf(c_31899,plain,
    ( ~ r4_lattice3(sK7,sK1(sK7,k15_lattice3(sK7,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8928,c_39,c_904,c_3366,c_30686])).

cnf(c_2799,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X3,X4,X2)
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_2797,plain,
    ( X0 != X1
    | sK1(X0,X2) = sK1(X1,X2) ),
    theory(equality)).

cnf(c_5804,plain,
    ( ~ r4_lattice3(X0,sK1(X1,X2),X3)
    | r4_lattice3(X4,sK1(X5,X2),X3)
    | X4 != X0
    | X5 != X1 ),
    inference(resolution,[status(thm)],[c_2799,c_2797])).

cnf(c_2789,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4821,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_2789,c_0])).

cnf(c_8346,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r2_hidden(X0,k1_xboole_0)
    | r2_hidden(k2_lattices(sK7,X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4821,c_862])).

cnf(c_3474,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3472])).

cnf(c_9124,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8346,c_3474])).

cnf(c_9136,plain,
    ( r4_lattice3(sK7,X0,k1_xboole_0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_9124,c_972])).

cnf(c_20466,plain,
    ( r4_lattice3(X0,sK1(X1,X2),k1_xboole_0)
    | ~ m1_subset_1(sK1(X3,X2),u1_struct_0(sK7))
    | X1 != X3
    | X0 != sK7 ),
    inference(resolution,[status(thm)],[c_5804,c_9136])).

cnf(c_20943,plain,
    ( r4_lattice3(X0,sK1(X1,X2),k1_xboole_0)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | v13_lattices(sK7)
    | X0 != sK7
    | X1 != sK7 ),
    inference(resolution,[status(thm)],[c_20466,c_1493])).

cnf(c_31915,plain,
    ( ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | v13_lattices(sK7)
    | sK7 != sK7 ),
    inference(resolution,[status(thm)],[c_31899,c_20943])).

cnf(c_31916,plain,
    ( ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | v13_lattices(sK7) ),
    inference(equality_resolution_simp,[status(thm)],[c_31915])).

cnf(c_10480,plain,
    ( m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31916,c_30686,c_10480])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.81/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.81/1.98  
% 11.81/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.81/1.98  
% 11.81/1.98  ------  iProver source info
% 11.81/1.98  
% 11.81/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.81/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.81/1.98  git: non_committed_changes: false
% 11.81/1.98  git: last_make_outside_of_git: false
% 11.81/1.98  
% 11.81/1.98  ------ 
% 11.81/1.98  ------ Parsing...
% 11.81/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.81/1.98  
% 11.81/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 11.81/1.98  
% 11.81/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.81/1.98  
% 11.81/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.81/1.98  ------ Proving...
% 11.81/1.98  ------ Problem Properties 
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  clauses                                 28
% 11.81/1.98  conjectures                             1
% 11.81/1.98  EPR                                     0
% 11.81/1.98  Horn                                    21
% 11.81/1.98  unary                                   6
% 11.81/1.98  binary                                  2
% 11.81/1.98  lits                                    81
% 11.81/1.98  lits eq                                 22
% 11.81/1.98  fd_pure                                 0
% 11.81/1.98  fd_pseudo                               0
% 11.81/1.98  fd_cond                                 3
% 11.81/1.98  fd_pseudo_cond                          3
% 11.81/1.98  AC symbols                              0
% 11.81/1.98  
% 11.81/1.98  ------ Input Options Time Limit: Unbounded
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  ------ 
% 11.81/1.98  Current options:
% 11.81/1.98  ------ 
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  ------ Proving...
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  % SZS status Theorem for theBenchmark.p
% 11.81/1.98  
% 11.81/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.81/1.98  
% 11.81/1.98  fof(f3,axiom,(
% 11.81/1.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.81/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f16,plain,(
% 11.81/1.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.81/1.98    inference(pure_predicate_removal,[],[f3])).
% 11.81/1.98  
% 11.81/1.98  fof(f17,plain,(
% 11.81/1.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.81/1.98    inference(pure_predicate_removal,[],[f16])).
% 11.81/1.98  
% 11.81/1.98  fof(f18,plain,(
% 11.81/1.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 11.81/1.98    inference(pure_predicate_removal,[],[f17])).
% 11.81/1.98  
% 11.81/1.98  fof(f19,plain,(
% 11.81/1.98    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 11.81/1.98    inference(ennf_transformation,[],[f18])).
% 11.81/1.98  
% 11.81/1.98  fof(f20,plain,(
% 11.81/1.98    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 11.81/1.98    inference(flattening,[],[f19])).
% 11.81/1.98  
% 11.81/1.98  fof(f75,plain,(
% 11.81/1.98    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f20])).
% 11.81/1.98  
% 11.81/1.98  fof(f7,axiom,(
% 11.81/1.98    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 11.81/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f26,plain,(
% 11.81/1.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 11.81/1.98    inference(ennf_transformation,[],[f7])).
% 11.81/1.98  
% 11.81/1.98  fof(f27,plain,(
% 11.81/1.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.98    inference(flattening,[],[f26])).
% 11.81/1.98  
% 11.81/1.98  fof(f46,plain,(
% 11.81/1.98    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.98    inference(nnf_transformation,[],[f27])).
% 11.81/1.98  
% 11.81/1.98  fof(f82,plain,(
% 11.81/1.98    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f46])).
% 11.81/1.98  
% 11.81/1.98  fof(f74,plain,(
% 11.81/1.98    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f20])).
% 11.81/1.98  
% 11.81/1.98  fof(f13,conjecture,(
% 11.81/1.98    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.81/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f14,negated_conjecture,(
% 11.81/1.98    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.81/1.98    inference(negated_conjecture,[],[f13])).
% 11.81/1.98  
% 11.81/1.98  fof(f38,plain,(
% 11.81/1.98    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.81/1.98    inference(ennf_transformation,[],[f14])).
% 11.81/1.98  
% 11.81/1.98  fof(f39,plain,(
% 11.81/1.98    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 11.81/1.98    inference(flattening,[],[f38])).
% 11.81/1.98  
% 11.81/1.98  fof(f66,plain,(
% 11.81/1.98    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) | ~l3_lattices(sK7) | ~v13_lattices(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f67,plain,(
% 11.81/1.99    (k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) | ~l3_lattices(sK7) | ~v13_lattices(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7)),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f66])).
% 11.81/1.99  
% 11.81/1.99  fof(f104,plain,(
% 11.81/1.99    v10_lattices(sK7)),
% 11.81/1.99    inference(cnf_transformation,[],[f67])).
% 11.81/1.99  
% 11.81/1.99  fof(f103,plain,(
% 11.81/1.99    ~v2_struct_0(sK7)),
% 11.81/1.99    inference(cnf_transformation,[],[f67])).
% 11.81/1.99  
% 11.81/1.99  fof(f106,plain,(
% 11.81/1.99    l3_lattices(sK7)),
% 11.81/1.99    inference(cnf_transformation,[],[f67])).
% 11.81/1.99  
% 11.81/1.99  fof(f11,axiom,(
% 11.81/1.99    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f34,plain,(
% 11.81/1.99    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f11])).
% 11.81/1.99  
% 11.81/1.99  fof(f35,plain,(
% 11.81/1.99    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(flattening,[],[f34])).
% 11.81/1.99  
% 11.81/1.99  fof(f61,plain,(
% 11.81/1.99    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(nnf_transformation,[],[f35])).
% 11.81/1.99  
% 11.81/1.99  fof(f62,plain,(
% 11.81/1.99    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(rectify,[],[f61])).
% 11.81/1.99  
% 11.81/1.99  fof(f64,plain,(
% 11.81/1.99    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK6(X0)) != k2_lattices(X0,sK6(X0),X1) & m1_subset_1(sK6(X0),u1_struct_0(X0))))) )),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f63,plain,(
% 11.81/1.99    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK5(X0)) != k2_lattices(X0,sK5(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f65,plain,(
% 11.81/1.99    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f62,f64,f63])).
% 11.81/1.99  
% 11.81/1.99  fof(f98,plain,(
% 11.81/1.99    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f65])).
% 11.81/1.99  
% 11.81/1.99  fof(f6,axiom,(
% 11.81/1.99    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f15,plain,(
% 11.81/1.99    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 11.81/1.99    inference(pure_predicate_removal,[],[f6])).
% 11.81/1.99  
% 11.81/1.99  fof(f25,plain,(
% 11.81/1.99    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 11.81/1.99    inference(ennf_transformation,[],[f15])).
% 11.81/1.99  
% 11.81/1.99  fof(f81,plain,(
% 11.81/1.99    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f25])).
% 11.81/1.99  
% 11.81/1.99  fof(f73,plain,(
% 11.81/1.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f20])).
% 11.81/1.99  
% 11.81/1.99  fof(f8,axiom,(
% 11.81/1.99    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f28,plain,(
% 11.81/1.99    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f8])).
% 11.81/1.99  
% 11.81/1.99  fof(f29,plain,(
% 11.81/1.99    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(flattening,[],[f28])).
% 11.81/1.99  
% 11.81/1.99  fof(f47,plain,(
% 11.81/1.99    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(nnf_transformation,[],[f29])).
% 11.81/1.99  
% 11.81/1.99  fof(f48,plain,(
% 11.81/1.99    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(rectify,[],[f47])).
% 11.81/1.99  
% 11.81/1.99  fof(f50,plain,(
% 11.81/1.99    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f49,plain,(
% 11.81/1.99    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f51,plain,(
% 11.81/1.99    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).
% 11.81/1.99  
% 11.81/1.99  fof(f88,plain,(
% 11.81/1.99    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f51])).
% 11.81/1.99  
% 11.81/1.99  fof(f87,plain,(
% 11.81/1.99    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f51])).
% 11.81/1.99  
% 11.81/1.99  fof(f12,axiom,(
% 11.81/1.99    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f36,plain,(
% 11.81/1.99    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f12])).
% 11.81/1.99  
% 11.81/1.99  fof(f37,plain,(
% 11.81/1.99    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(flattening,[],[f36])).
% 11.81/1.99  
% 11.81/1.99  fof(f102,plain,(
% 11.81/1.99    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f37])).
% 11.81/1.99  
% 11.81/1.99  fof(f10,axiom,(
% 11.81/1.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f32,plain,(
% 11.81/1.99    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f10])).
% 11.81/1.99  
% 11.81/1.99  fof(f33,plain,(
% 11.81/1.99    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(flattening,[],[f32])).
% 11.81/1.99  
% 11.81/1.99  fof(f56,plain,(
% 11.81/1.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(nnf_transformation,[],[f33])).
% 11.81/1.99  
% 11.81/1.99  fof(f57,plain,(
% 11.81/1.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(flattening,[],[f56])).
% 11.81/1.99  
% 11.81/1.99  fof(f58,plain,(
% 11.81/1.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(rectify,[],[f57])).
% 11.81/1.99  
% 11.81/1.99  fof(f59,plain,(
% 11.81/1.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f60,plain,(
% 11.81/1.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).
% 11.81/1.99  
% 11.81/1.99  fof(f94,plain,(
% 11.81/1.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f60])).
% 11.81/1.99  
% 11.81/1.99  fof(f112,plain,(
% 11.81/1.99    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(equality_resolution,[],[f94])).
% 11.81/1.99  
% 11.81/1.99  fof(f105,plain,(
% 11.81/1.99    v4_lattice3(sK7)),
% 11.81/1.99    inference(cnf_transformation,[],[f67])).
% 11.81/1.99  
% 11.81/1.99  fof(f95,plain,(
% 11.81/1.99    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f60])).
% 11.81/1.99  
% 11.81/1.99  fof(f9,axiom,(
% 11.81/1.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f30,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f9])).
% 11.81/1.99  
% 11.81/1.99  fof(f31,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(flattening,[],[f30])).
% 11.81/1.99  
% 11.81/1.99  fof(f52,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(nnf_transformation,[],[f31])).
% 11.81/1.99  
% 11.81/1.99  fof(f53,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(rectify,[],[f52])).
% 11.81/1.99  
% 11.81/1.99  fof(f54,plain,(
% 11.81/1.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f55,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).
% 11.81/1.99  
% 11.81/1.99  fof(f91,plain,(
% 11.81/1.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f55])).
% 11.81/1.99  
% 11.81/1.99  fof(f1,axiom,(
% 11.81/1.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f40,plain,(
% 11.81/1.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 11.81/1.99    inference(nnf_transformation,[],[f1])).
% 11.81/1.99  
% 11.81/1.99  fof(f41,plain,(
% 11.81/1.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 11.81/1.99    inference(flattening,[],[f40])).
% 11.81/1.99  
% 11.81/1.99  fof(f70,plain,(
% 11.81/1.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 11.81/1.99    inference(cnf_transformation,[],[f41])).
% 11.81/1.99  
% 11.81/1.99  fof(f108,plain,(
% 11.81/1.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.81/1.99    inference(equality_resolution,[],[f70])).
% 11.81/1.99  
% 11.81/1.99  fof(f2,axiom,(
% 11.81/1.99    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f71,plain,(
% 11.81/1.99    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 11.81/1.99    inference(cnf_transformation,[],[f2])).
% 11.81/1.99  
% 11.81/1.99  fof(f86,plain,(
% 11.81/1.99    ( ! [X4,X0] : (k2_lattices(X0,X4,sK2(X0)) = sK2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f51])).
% 11.81/1.99  
% 11.81/1.99  fof(f5,axiom,(
% 11.81/1.99    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f23,plain,(
% 11.81/1.99    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f5])).
% 11.81/1.99  
% 11.81/1.99  fof(f24,plain,(
% 11.81/1.99    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(flattening,[],[f23])).
% 11.81/1.99  
% 11.81/1.99  fof(f80,plain,(
% 11.81/1.99    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f24])).
% 11.81/1.99  
% 11.81/1.99  fof(f107,plain,(
% 11.81/1.99    k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) | ~l3_lattices(sK7) | ~v13_lattices(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)),
% 11.81/1.99    inference(cnf_transformation,[],[f67])).
% 11.81/1.99  
% 11.81/1.99  fof(f83,plain,(
% 11.81/1.99    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f46])).
% 11.81/1.99  
% 11.81/1.99  fof(f4,axiom,(
% 11.81/1.99    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f21,plain,(
% 11.81/1.99    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.81/1.99    inference(ennf_transformation,[],[f4])).
% 11.81/1.99  
% 11.81/1.99  fof(f22,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(flattening,[],[f21])).
% 11.81/1.99  
% 11.81/1.99  fof(f42,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(nnf_transformation,[],[f22])).
% 11.81/1.99  
% 11.81/1.99  fof(f43,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(rectify,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  fof(f44,plain,(
% 11.81/1.99    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f45,plain,(
% 11.81/1.99    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 11.81/1.99  
% 11.81/1.99  fof(f76,plain,(
% 11.81/1.99    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f45])).
% 11.81/1.99  
% 11.81/1.99  fof(f111,plain,(
% 11.81/1.99    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(equality_resolution,[],[f76])).
% 11.81/1.99  
% 11.81/1.99  fof(f97,plain,(
% 11.81/1.99    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK4(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f60])).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2787,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2786,plain,( X0 = X0 ),theory(equality) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_4628,plain,
% 11.81/1.99      ( X0 != X1 | X1 = X0 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_2787,c_2786]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_4,plain,
% 11.81/1.99      ( ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | v9_lattices(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_15,plain,
% 11.81/1.99      ( ~ r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ v8_lattices(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v9_lattices(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) = X1 ),
% 11.81/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_494,plain,
% 11.81/1.99      ( ~ r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ v8_lattices(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) = X1 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_4,c_15]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_5,plain,
% 11.81/1.99      ( v8_lattices(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_498,plain,
% 11.81/1.99      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) = X1 ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_494,c_5]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_499,plain,
% 11.81/1.99      ( ~ r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) = X1 ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_498]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_38,negated_conjecture,
% 11.81/1.99      ( v10_lattices(sK7) ),
% 11.81/1.99      inference(cnf_transformation,[],[f104]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_856,plain,
% 11.81/1.99      ( ~ r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) = X1
% 11.81/1.99      | sK7 != X0 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_499,c_38]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_857,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | ~ l3_lattices(sK7)
% 11.81/1.99      | v2_struct_0(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,X1) = X0 ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_856]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_39,negated_conjecture,
% 11.81/1.99      ( ~ v2_struct_0(sK7) ),
% 11.81/1.99      inference(cnf_transformation,[],[f103]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_36,negated_conjecture,
% 11.81/1.99      ( l3_lattices(sK7) ),
% 11.81/1.99      inference(cnf_transformation,[],[f106]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_861,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | k2_lattices(sK7,X0,X1) = X0 ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_857,c_39,c_36]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_862,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | k2_lattices(sK7,X0,X1) = X0 ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_861]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_6897,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | X0 = k2_lattices(sK7,X0,X1) ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_4628,c_862]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_33,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | ~ v6_lattices(X1)
% 11.81/1.99      | v2_struct_0(X1)
% 11.81/1.99      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 11.81/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1427,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | ~ v6_lattices(X1)
% 11.81/1.99      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 11.81/1.99      | sK7 != X1 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_33,c_39]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1428,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | ~ l1_lattices(sK7)
% 11.81/1.99      | ~ v6_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,X1) = k2_lattices(sK7,X1,X0) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_1427]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_13,plain,
% 11.81/1.99      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_109,plain,
% 11.81/1.99      ( l1_lattices(sK7) | ~ l3_lattices(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_6,plain,
% 11.81/1.99      ( v6_lattices(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_880,plain,
% 11.81/1.99      ( v6_lattices(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | sK7 != X0 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_6,c_38]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_881,plain,
% 11.81/1.99      ( v6_lattices(sK7) | ~ l3_lattices(sK7) | v2_struct_0(sK7) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_880]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_128,plain,
% 11.81/1.99      ( v6_lattices(sK7)
% 11.81/1.99      | ~ l3_lattices(sK7)
% 11.81/1.99      | v2_struct_0(sK7)
% 11.81/1.99      | ~ v10_lattices(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_883,plain,
% 11.81/1.99      ( v6_lattices(sK7) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_881,c_39,c_38,c_36,c_128]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1152,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | v2_struct_0(X1)
% 11.81/1.99      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 11.81/1.99      | sK7 != X1 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_33,c_883]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1153,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | ~ l1_lattices(sK7)
% 11.81/1.99      | v2_struct_0(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,X1) = k2_lattices(sK7,X1,X0) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_1152]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1431,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | k2_lattices(sK7,X0,X1) = k2_lattices(sK7,X1,X0) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_1428,c_39,c_36,c_109,c_1153]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1432,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | k2_lattices(sK7,X1,X0) = k2_lattices(sK7,X0,X1) ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_1431]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_4635,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | X2 != k2_lattices(sK7,X1,X0)
% 11.81/1.99      | k2_lattices(sK7,X0,X1) = X2 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_2787,c_1432]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_7173,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | k2_lattices(sK7,X1,X0) = X0 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_6897,c_4635]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_16,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | v13_lattices(X1)
% 11.81/1.99      | v2_struct_0(X1)
% 11.81/1.99      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 11.81/1.99      | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
% 11.81/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1508,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | v13_lattices(X1)
% 11.81/1.99      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 11.81/1.99      | k2_lattices(X1,sK1(X1,X0),X0) != X0
% 11.81/1.99      | sK7 != X1 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_16,c_39]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1509,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ l1_lattices(sK7)
% 11.81/1.99      | v13_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0
% 11.81/1.99      | k2_lattices(sK7,sK1(sK7,X0),X0) != X0 ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_1508]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1513,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0
% 11.81/1.99      | k2_lattices(sK7,sK1(sK7,X0),X0) != X0 ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_1509,c_36,c_109]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_8026,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,sK1(sK7,X0))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_7173,c_1513]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_17,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | v13_lattices(X1)
% 11.81/1.99      | v2_struct_0(X1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1487,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | v13_lattices(X1)
% 11.81/1.99      | sK7 != X1 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_39]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1488,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
% 11.81/1.99      | ~ l1_lattices(sK7)
% 11.81/1.99      | v13_lattices(sK7) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_1487]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1492,plain,
% 11.81/1.99      ( m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_1488,c_36,c_109]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1493,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7) ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_1492]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_8225,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ r1_lattices(sK7,X0,sK1(sK7,X0))
% 11.81/1.99      | v13_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0 ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_8026,c_1493]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_8226,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,sK1(sK7,X0))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,sK1(sK7,X0)) != X0 ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_8225]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_8688,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,sK1(sK7,X0))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(sK1(sK7,X0),u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7) ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_8226,c_862]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_8702,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ r1_lattices(sK7,X0,sK1(sK7,X0))
% 11.81/1.99      | v13_lattices(sK7) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_8688,c_1493]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_8703,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,sK1(sK7,X0))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7) ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_8702]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_34,plain,
% 11.81/1.99      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f102]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_903,plain,
% 11.81/1.99      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | sK7 != X0 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_34,c_36]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_904,plain,
% 11.81/1.99      ( m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
% 11.81/1.99      | v2_struct_0(sK7) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_903]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_908,plain,
% 11.81/1.99      ( m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7)) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_904,c_39]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_28,plain,
% 11.81/1.99      ( ~ r4_lattice3(X0,X1,X2)
% 11.81/1.99      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 11.81/1.99      | ~ v4_lattice3(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f112]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_37,negated_conjecture,
% 11.81/1.99      ( v4_lattice3(sK7) ),
% 11.81/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_714,plain,
% 11.81/1.99      ( ~ r4_lattice3(X0,X1,X2)
% 11.81/1.99      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | sK7 != X0 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_715,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | r1_lattices(sK7,k15_lattice3(sK7,X1),X0)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
% 11.81/1.99      | ~ l3_lattices(sK7)
% 11.81/1.99      | v2_struct_0(sK7)
% 11.81/1.99      | ~ v10_lattices(sK7) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_714]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_719,plain,
% 11.81/1.99      ( ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | r1_lattices(sK7,k15_lattice3(sK7,X1),X0)
% 11.81/1.99      | ~ r4_lattice3(sK7,X0,X1) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_715,c_39,c_38,c_36]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_720,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | r1_lattices(sK7,k15_lattice3(sK7,X1),X0)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7)) ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_719]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1016,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | r1_lattices(sK7,k15_lattice3(sK7,X1),X0)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 11.81/1.99      inference(backward_subsumption_resolution,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_908,c_720]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_8928,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,sK1(sK7,k15_lattice3(sK7,X0)),X0)
% 11.81/1.99      | ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(sK1(sK7,k15_lattice3(sK7,X0)),u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7) ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_8703,c_1016]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3366,plain,
% 11.81/1.99      ( ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
% 11.81/1.99      | m1_subset_1(sK1(sK7,k15_lattice3(sK7,X0)),u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_1493]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_27,plain,
% 11.81/1.99      ( ~ r4_lattice3(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
% 11.81/1.99      | ~ v4_lattice3(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k15_lattice3(X0,X2) = X1 ),
% 11.81/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_738,plain,
% 11.81/1.99      ( ~ r4_lattice3(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k15_lattice3(X0,X2) = X1
% 11.81/1.99      | sK7 != X0 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_27,c_37]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_739,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
% 11.81/1.99      | ~ l3_lattices(sK7)
% 11.81/1.99      | v2_struct_0(sK7)
% 11.81/1.99      | ~ v10_lattices(sK7)
% 11.81/1.99      | k15_lattice3(sK7,X1) = X0 ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_738]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_743,plain,
% 11.81/1.99      ( m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | k15_lattice3(sK7,X1) = X0 ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_739,c_39,c_38,c_36]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_744,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
% 11.81/1.99      | k15_lattice3(sK7,X1) = X0 ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_743]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3290,plain,
% 11.81/1.99      ( k15_lattice3(sK7,X0) = X1
% 11.81/1.99      | r4_lattice3(sK7,X1,X0) != iProver_top
% 11.81/1.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 11.81/1.99      | m1_subset_1(sK4(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_22,plain,
% 11.81/1.99      ( r4_lattice3(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | r2_hidden(sK3(X0,X1,X2),X2)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_966,plain,
% 11.81/1.99      ( r4_lattice3(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | r2_hidden(sK3(X0,X1,X2),X2)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | sK7 != X0 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_967,plain,
% 11.81/1.99      ( r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | r2_hidden(sK3(sK7,X0,X1),X1)
% 11.81/1.99      | v2_struct_0(sK7) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_966]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_971,plain,
% 11.81/1.99      ( r2_hidden(sK3(sK7,X0,X1),X1)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | r4_lattice3(sK7,X0,X1) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_967,c_39]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_972,plain,
% 11.81/1.99      ( r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | r2_hidden(sK3(sK7,X0,X1),X1) ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_971]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3282,plain,
% 11.81/1.99      ( r4_lattice3(sK7,X0,X1) = iProver_top
% 11.81/1.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 11.81/1.99      | r2_hidden(sK3(sK7,X0,X1),X1) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_972]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_0,plain,
% 11.81/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.81/1.99      inference(cnf_transformation,[],[f108]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3,plain,
% 11.81/1.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 11.81/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3293,plain,
% 11.81/1.99      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3472,plain,
% 11.81/1.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_0,c_3293]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_4982,plain,
% 11.81/1.99      ( r4_lattice3(sK7,X0,k1_xboole_0) = iProver_top
% 11.81/1.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_3282,c_3472]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_7245,plain,
% 11.81/1.99      ( k15_lattice3(sK7,X0) = X1
% 11.81/1.99      | r4_lattice3(sK7,X1,X0) != iProver_top
% 11.81/1.99      | r4_lattice3(sK7,sK4(sK7,X0,X1),k1_xboole_0) = iProver_top
% 11.81/1.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_3290,c_4982]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_18,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | ~ v13_lattices(X1)
% 11.81/1.99      | v2_struct_0(X1)
% 11.81/1.99      | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1466,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | ~ v13_lattices(X1)
% 11.81/1.99      | k2_lattices(X1,X0,sK2(X1)) = sK2(X1)
% 11.81/1.99      | sK7 != X1 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1467,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ l1_lattices(sK7)
% 11.81/1.99      | ~ v13_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,sK2(sK7)) = sK2(sK7) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_1466]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1471,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ v13_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,sK2(sK7)) = sK2(sK7) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_1467,c_36,c_109]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3275,plain,
% 11.81/1.99      ( k2_lattices(sK7,X0,sK2(sK7)) = sK2(sK7)
% 11.81/1.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 11.81/1.99      | v13_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_1471]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_7250,plain,
% 11.81/1.99      ( k2_lattices(sK7,sK4(sK7,X0,X1),sK2(sK7)) = sK2(sK7)
% 11.81/1.99      | k15_lattice3(sK7,X0) = X1
% 11.81/1.99      | r4_lattice3(sK7,X1,X0) != iProver_top
% 11.81/1.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 11.81/1.99      | v13_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_3290,c_3275]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_27703,plain,
% 11.81/1.99      ( sK4(sK7,X0,X1) = k15_lattice3(sK7,k1_xboole_0)
% 11.81/1.99      | k2_lattices(sK7,sK4(sK7,k1_xboole_0,sK4(sK7,X0,X1)),sK2(sK7)) = sK2(sK7)
% 11.81/1.99      | k15_lattice3(sK7,X0) = X1
% 11.81/1.99      | r4_lattice3(sK7,X1,X0) != iProver_top
% 11.81/1.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 11.81/1.99      | m1_subset_1(sK4(sK7,X0,X1),u1_struct_0(sK7)) != iProver_top
% 11.81/1.99      | v13_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_7245,c_7250]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_12,plain,
% 11.81/1.99      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 11.81/1.99      | ~ l1_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_112,plain,
% 11.81/1.99      ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
% 11.81/1.99      | ~ l1_lattices(sK7)
% 11.81/1.99      | v2_struct_0(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_35,negated_conjecture,
% 11.81/1.99      ( ~ v13_lattices(sK7)
% 11.81/1.99      | ~ l3_lattices(sK7)
% 11.81/1.99      | v2_struct_0(sK7)
% 11.81/1.99      | ~ v10_lattices(sK7)
% 11.81/1.99      | k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) ),
% 11.81/1.99      inference(cnf_transformation,[],[f107]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_221,negated_conjecture,
% 11.81/1.99      ( ~ v13_lattices(sK7)
% 11.81/1.99      | k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_35,c_39,c_38,c_36]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_223,plain,
% 11.81/1.99      ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
% 11.81/1.99      | v13_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2790,plain,
% 11.81/1.99      ( X0 != X1 | k5_lattices(X0) = k5_lattices(X1) ),
% 11.81/1.99      theory(equality) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2805,plain,
% 11.81/1.99      ( k5_lattices(sK7) = k5_lattices(sK7) | sK7 != sK7 ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_2790]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2819,plain,
% 11.81/1.99      ( sK7 = sK7 ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_2786]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3575,plain,
% 11.81/1.99      ( k15_lattice3(sK7,k1_xboole_0) != X0
% 11.81/1.99      | k5_lattices(sK7) != X0
% 11.81/1.99      | k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_2787]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3705,plain,
% 11.81/1.99      ( k15_lattice3(sK7,k1_xboole_0) != k5_lattices(sK7)
% 11.81/1.99      | k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0)
% 11.81/1.99      | k5_lattices(sK7) != k5_lattices(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_3575]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1416,plain,
% 11.81/1.99      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 11.81/1.99      | ~ l1_lattices(X0)
% 11.81/1.99      | sK7 != X0 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_12,c_39]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1417,plain,
% 11.81/1.99      ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
% 11.81/1.99      | ~ l1_lattices(sK7) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_1416]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1419,plain,
% 11.81/1.99      ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_1417,c_39,c_36,c_109,c_112]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3277,plain,
% 11.81/1.99      ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_1419]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_5164,plain,
% 11.81/1.99      ( r4_lattice3(sK7,k5_lattices(sK7),k1_xboole_0) = iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_3277,c_4982]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_5170,plain,
% 11.81/1.99      ( r4_lattice3(sK7,k5_lattices(sK7),k1_xboole_0) ),
% 11.81/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_5164]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3911,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,k5_lattices(sK7),X0)
% 11.81/1.99      | m1_subset_1(sK4(sK7,X0,k5_lattices(sK7)),u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
% 11.81/1.99      | k15_lattice3(sK7,X0) = k5_lattices(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_744]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_7404,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,k5_lattices(sK7),k1_xboole_0)
% 11.81/1.99      | m1_subset_1(sK4(sK7,k1_xboole_0,k5_lattices(sK7)),u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
% 11.81/1.99      | k15_lattice3(sK7,k1_xboole_0) = k5_lattices(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_3911]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_14,plain,
% 11.81/1.99      ( r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ v8_lattices(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v9_lattices(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) != X1 ),
% 11.81/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_526,plain,
% 11.81/1.99      ( r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ v8_lattices(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) != X1 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_4,c_14]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_530,plain,
% 11.81/1.99      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) != X1 ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_526,c_5]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_531,plain,
% 11.81/1.99      ( r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) != X1 ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_530]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_832,plain,
% 11.81/1.99      ( r1_lattices(X0,X1,X2)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | k2_lattices(X0,X1,X2) != X1
% 11.81/1.99      | sK7 != X0 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_531,c_38]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_833,plain,
% 11.81/1.99      ( r1_lattices(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | ~ l3_lattices(sK7)
% 11.81/1.99      | v2_struct_0(sK7)
% 11.81/1.99      | k2_lattices(sK7,X0,X1) != X0 ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_832]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_837,plain,
% 11.81/1.99      ( r1_lattices(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | k2_lattices(sK7,X0,X1) != X0 ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_833,c_39,c_36]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_838,plain,
% 11.81/1.99      ( r1_lattices(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | k2_lattices(sK7,X0,X1) != X0 ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_837]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3411,plain,
% 11.81/1.99      ( r1_lattices(sK7,k5_lattices(sK7),X0)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
% 11.81/1.99      | k2_lattices(sK7,k5_lattices(sK7),X0) != k5_lattices(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_838]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_22722,plain,
% 11.81/1.99      ( r1_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7)))
% 11.81/1.99      | ~ m1_subset_1(sK4(sK7,k1_xboole_0,k5_lattices(sK7)),u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
% 11.81/1.99      | k2_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7))) != k5_lattices(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_3411]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_11,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | ~ v13_lattices(X1)
% 11.81/1.99      | v2_struct_0(X1)
% 11.81/1.99      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
% 11.81/1.99      inference(cnf_transformation,[],[f111]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1532,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.81/1.99      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 11.81/1.99      | ~ l1_lattices(X1)
% 11.81/1.99      | ~ v13_lattices(X1)
% 11.81/1.99      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
% 11.81/1.99      | sK7 != X1 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_39]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1533,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
% 11.81/1.99      | ~ l1_lattices(sK7)
% 11.81/1.99      | ~ v13_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,k5_lattices(sK7),X0) = k5_lattices(sK7) ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_1532]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_1537,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ v13_lattices(sK7)
% 11.81/1.99      | k2_lattices(sK7,k5_lattices(sK7),X0) = k5_lattices(sK7) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_1533,c_39,c_36,c_109,c_112]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3272,plain,
% 11.81/1.99      ( k2_lattices(sK7,k5_lattices(sK7),X0) = k5_lattices(sK7)
% 11.81/1.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 11.81/1.99      | v13_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_1537]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_7251,plain,
% 11.81/1.99      ( k2_lattices(sK7,k5_lattices(sK7),sK4(sK7,X0,X1)) = k5_lattices(sK7)
% 11.81/1.99      | k15_lattice3(sK7,X0) = X1
% 11.81/1.99      | r4_lattice3(sK7,X1,X0) != iProver_top
% 11.81/1.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 11.81/1.99      | v13_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_3290,c_3272]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_28449,plain,
% 11.81/1.99      ( k2_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7))) = k5_lattices(sK7)
% 11.81/1.99      | k15_lattice3(sK7,k1_xboole_0) = k5_lattices(sK7)
% 11.81/1.99      | m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) != iProver_top
% 11.81/1.99      | v13_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(superposition,[status(thm)],[c_5164,c_7251]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_40,plain,
% 11.81/1.99      ( v2_struct_0(sK7) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_43,plain,
% 11.81/1.99      ( l3_lattices(sK7) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_108,plain,
% 11.81/1.99      ( l1_lattices(X0) = iProver_top | l3_lattices(X0) != iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_110,plain,
% 11.81/1.99      ( l1_lattices(sK7) = iProver_top
% 11.81/1.99      | l3_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_108]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_111,plain,
% 11.81/1.99      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) = iProver_top
% 11.81/1.99      | l1_lattices(X0) != iProver_top
% 11.81/1.99      | v2_struct_0(X0) = iProver_top ),
% 11.81/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_113,plain,
% 11.81/1.99      ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) = iProver_top
% 11.81/1.99      | l1_lattices(sK7) != iProver_top
% 11.81/1.99      | v2_struct_0(sK7) = iProver_top ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_111]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_28749,plain,
% 11.81/1.99      ( k2_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7))) = k5_lattices(sK7)
% 11.81/1.99      | v13_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_28449,c_40,c_43,c_110,c_113,c_223,c_2805,c_2819,
% 11.81/1.99                 c_3705]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_25,plain,
% 11.81/1.99      ( ~ r4_lattice3(X0,X1,X2)
% 11.81/1.99      | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ v4_lattice3(X0)
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k15_lattice3(X0,X2) = X1 ),
% 11.81/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_786,plain,
% 11.81/1.99      ( ~ r4_lattice3(X0,X1,X2)
% 11.81/1.99      | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.81/1.99      | ~ l3_lattices(X0)
% 11.81/1.99      | v2_struct_0(X0)
% 11.81/1.99      | ~ v10_lattices(X0)
% 11.81/1.99      | k15_lattice3(X0,X2) = X1
% 11.81/1.99      | sK7 != X0 ),
% 11.81/1.99      inference(resolution_lifted,[status(thm)],[c_25,c_37]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_787,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ l3_lattices(sK7)
% 11.81/1.99      | v2_struct_0(sK7)
% 11.81/1.99      | ~ v10_lattices(sK7)
% 11.81/1.99      | k15_lattice3(sK7,X1) = X0 ),
% 11.81/1.99      inference(unflattening,[status(thm)],[c_786]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_791,plain,
% 11.81/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
% 11.81/1.99      | ~ r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | k15_lattice3(sK7,X1) = X0 ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_787,c_39,c_38,c_36]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_792,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,X0,X1)
% 11.81/1.99      | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | k15_lattice3(sK7,X1) = X0 ),
% 11.81/1.99      inference(renaming,[status(thm)],[c_791]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_30590,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,k5_lattices(sK7),k1_xboole_0)
% 11.81/1.99      | ~ r1_lattices(sK7,k5_lattices(sK7),sK4(sK7,k1_xboole_0,k5_lattices(sK7)))
% 11.81/1.99      | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
% 11.81/1.99      | k15_lattice3(sK7,k1_xboole_0) = k5_lattices(sK7) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_792]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_30684,plain,
% 11.81/1.99      ( v13_lattices(sK7) != iProver_top ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_27703,c_39,c_36,c_109,c_112,c_223,c_2805,c_2819,
% 11.81/1.99                 c_3705,c_5170,c_7404,c_22722,c_28749,c_30590]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_30686,plain,
% 11.81/1.99      ( ~ v13_lattices(sK7) ),
% 11.81/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_30684]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_31899,plain,
% 11.81/1.99      ( ~ r4_lattice3(sK7,sK1(sK7,k15_lattice3(sK7,X0)),X0) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_8928,c_39,c_904,c_3366,c_30686]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2799,plain,
% 11.81/1.99      ( ~ r4_lattice3(X0,X1,X2)
% 11.81/1.99      | r4_lattice3(X3,X4,X2)
% 11.81/1.99      | X3 != X0
% 11.81/1.99      | X4 != X1 ),
% 11.81/1.99      theory(equality) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2797,plain,
% 11.81/1.99      ( X0 != X1 | sK1(X0,X2) = sK1(X1,X2) ),
% 11.81/1.99      theory(equality) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_5804,plain,
% 11.81/1.99      ( ~ r4_lattice3(X0,sK1(X1,X2),X3)
% 11.81/1.99      | r4_lattice3(X4,sK1(X5,X2),X3)
% 11.81/1.99      | X4 != X0
% 11.81/1.99      | X5 != X1 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_2799,c_2797]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_2789,plain,
% 11.81/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.81/1.99      theory(equality) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_4821,plain,
% 11.81/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
% 11.81/1.99      | ~ r2_hidden(X2,k1_xboole_0)
% 11.81/1.99      | X0 != X2 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_2789,c_0]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_8346,plain,
% 11.81/1.99      ( ~ r1_lattices(sK7,X0,X1)
% 11.81/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.81/1.99      | ~ r2_hidden(X0,k1_xboole_0)
% 11.81/1.99      | r2_hidden(k2_lattices(sK7,X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_4821,c_862]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_3474,plain,
% 11.81/1.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 11.81/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_3472]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_9124,plain,
% 11.81/1.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 11.81/1.99      inference(global_propositional_subsumption,
% 11.81/1.99                [status(thm)],
% 11.81/1.99                [c_8346,c_3474]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_9136,plain,
% 11.81/1.99      ( r4_lattice3(sK7,X0,k1_xboole_0)
% 11.81/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_9124,c_972]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_20466,plain,
% 11.81/1.99      ( r4_lattice3(X0,sK1(X1,X2),k1_xboole_0)
% 11.81/1.99      | ~ m1_subset_1(sK1(X3,X2),u1_struct_0(sK7))
% 11.81/1.99      | X1 != X3
% 11.81/1.99      | X0 != sK7 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_5804,c_9136]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_20943,plain,
% 11.81/1.99      ( r4_lattice3(X0,sK1(X1,X2),k1_xboole_0)
% 11.81/1.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7)
% 11.81/1.99      | X0 != sK7
% 11.81/1.99      | X1 != sK7 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_20466,c_1493]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_31915,plain,
% 11.81/1.99      ( ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7)
% 11.81/1.99      | sK7 != sK7 ),
% 11.81/1.99      inference(resolution,[status(thm)],[c_31899,c_20943]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_31916,plain,
% 11.81/1.99      ( ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
% 11.81/1.99      | v13_lattices(sK7) ),
% 11.81/1.99      inference(equality_resolution_simp,[status(thm)],[c_31915]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(c_10480,plain,
% 11.81/1.99      ( m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) ),
% 11.81/1.99      inference(instantiation,[status(thm)],[c_908]) ).
% 11.81/1.99  
% 11.81/1.99  cnf(contradiction,plain,
% 11.81/1.99      ( $false ),
% 11.81/1.99      inference(minisat,[status(thm)],[c_31916,c_30686,c_10480]) ).
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.81/1.99  
% 11.81/1.99  ------                               Statistics
% 11.81/1.99  
% 11.81/1.99  ------ Selected
% 11.81/1.99  
% 11.81/1.99  total_time:                             1.202
% 11.81/1.99  
%------------------------------------------------------------------------------
