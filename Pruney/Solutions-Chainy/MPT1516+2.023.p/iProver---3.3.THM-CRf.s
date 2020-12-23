%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:20 EST 2020

% Result     : Theorem 23.54s
% Output     : CNFRefutation 23.54s
% Verified   : 
% Statistics : Number of formulae       :  256 (6258 expanded)
%              Number of clauses        :  161 (1862 expanded)
%              Number of leaves         :   28 (1246 expanded)
%              Depth                    :   30
%              Number of atoms          : 1127 (40290 expanded)
%              Number of equality atoms :  304 (5231 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f69,plain,
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
   => ( ( k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0)
        | ~ l3_lattices(sK8)
        | ~ v13_lattices(sK8)
        | ~ v10_lattices(sK8)
        | v2_struct_0(sK8) )
      & l3_lattices(sK8)
      & v4_lattice3(sK8)
      & v10_lattices(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ( k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0)
      | ~ l3_lattices(sK8)
      | ~ v13_lattices(sK8)
      | ~ v10_lattices(sK8)
      | v2_struct_0(sK8) )
    & l3_lattices(sK8)
    & v4_lattice3(sK8)
    & v10_lattices(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f45,f69])).

fof(f110,plain,(
    l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f70])).

fof(f107,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f70])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( k2_lattices(X0,X4,sK4(X0)) = sK4(X0)
              & k2_lattices(X0,sK4(X0),X4) = sK4(X0) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK3(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK3(X0,X1)) != X1 )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK3(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK3(X0,X1)) != X1 )
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( k2_lattices(X0,X4,sK4(X0)) = sK4(X0)
                  & k2_lattices(X0,sK4(X0),X4) = sK4(X0) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f58,f60,f59])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    v4_lattice3(sK8) ),
    inference(cnf_transformation,[],[f70])).

fof(f108,plain,(
    v10_lattices(sK8) ),
    inference(cnf_transformation,[],[f70])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK6(X0)) != k2_lattices(X0,sK6(X0),X1)
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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

fof(f66,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f63,f65,f64])).

fof(f97,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

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

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f21])).

fof(f74,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f111,plain,
    ( k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0)
    | ~ l3_lattices(sK8)
    | ~ v13_lattices(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f70])).

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

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f112,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f67,plain,(
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
            | ~ r3_lattices(X0,sK7(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X0,sK7(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(sK7(X0,X1,X2),X1)
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f67])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f75,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f76,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK2(X0))) != X1
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK1(X0),k1_lattices(X0,sK1(X0),X2)) != sK1(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK1(X0),k1_lattices(X0,sK1(X0),sK2(X0))) != sK1(X0)
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f52,f54,f53])).

fof(f83,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK3(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_30,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_37,negated_conjecture,
    ( l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_959,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_37])).

cnf(c_960,plain,
    ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8))
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_959])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_964,plain,
    ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_960,c_40])).

cnf(c_2342,plain,
    ( m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_964])).

cnf(c_2736,plain,
    ( m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2342])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1277,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_40])).

cnf(c_1278,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8,X0),u1_struct_0(sK8))
    | ~ l1_lattices(sK8)
    | v13_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_1277])).

cnf(c_18,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_98,plain,
    ( l1_lattices(sK8)
    | ~ l3_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1282,plain,
    ( m1_subset_1(sK3(sK8,X0),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v13_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1278,c_37,c_98])).

cnf(c_1283,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8,X0),u1_struct_0(sK8))
    | v13_lattices(sK8) ),
    inference(renaming,[status(thm)],[c_1282])).

cnf(c_2333,plain,
    ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8,X0_60),u1_struct_0(sK8))
    | v13_lattices(sK8) ),
    inference(subtyping,[status(esa)],[c_1283])).

cnf(c_2745,plain,
    ( m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8,X0_60),u1_struct_0(sK8)) = iProver_top
    | v13_lattices(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2333])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_38,negated_conjecture,
    ( v4_lattice3(sK8) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_38])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ v10_lattices(sK8)
    | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_39,negated_conjecture,
    ( v10_lattices(sK8) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_40,c_39,c_37])).

cnf(c_2346,plain,
    ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
    | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X0_60)) = X0_60 ),
    inference(subtyping,[status(esa)],[c_744])).

cnf(c_2732,plain,
    ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X0_60)) = X0_60
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2346])).

cnf(c_3378,plain,
    ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK3(sK8,X0_60))) = sK3(sK8,X0_60)
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2745,c_2732])).

cnf(c_6352,plain,
    ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK3(sK8,k15_lattice3(sK8,X0_63)))) = sK3(sK8,k15_lattice3(sK8,X0_63))
    | v13_lattices(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2736,c_3378])).

cnf(c_25,plain,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | ~ v13_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1192,plain,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | ~ v13_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_40])).

cnf(c_1193,plain,
    ( m1_subset_1(sK4(sK8),u1_struct_0(sK8))
    | ~ l1_lattices(sK8)
    | ~ v13_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_1192])).

cnf(c_1195,plain,
    ( m1_subset_1(sK4(sK8),u1_struct_0(sK8))
    | ~ v13_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1193,c_37,c_98])).

cnf(c_2337,plain,
    ( m1_subset_1(sK4(sK8),u1_struct_0(sK8))
    | ~ v13_lattices(sK8) ),
    inference(subtyping,[status(esa)],[c_1195])).

cnf(c_2741,plain,
    ( m1_subset_1(sK4(sK8),u1_struct_0(sK8)) = iProver_top
    | v13_lattices(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2337])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1217,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_40])).

cnf(c_1218,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_lattices(sK8)
    | ~ v6_lattices(sK8)
    | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1217])).

cnf(c_4,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_875,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_39])).

cnf(c_876,plain,
    ( v6_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_875])).

cnf(c_138,plain,
    ( v6_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ v10_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_878,plain,
    ( v6_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_876,c_40,c_39,c_37,c_138])).

cnf(c_1144,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_878])).

cnf(c_1145,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_lattices(sK8)
    | v2_struct_0(sK8)
    | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1144])).

cnf(c_1149,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1145,c_40,c_37,c_98])).

cnf(c_1221,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1218,c_40,c_37,c_98,c_1145])).

cnf(c_2338,plain,
    ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_60,u1_struct_0(sK8))
    | k2_lattices(sK8,X1_60,X0_60) = k2_lattices(sK8,X0_60,X1_60) ),
    inference(subtyping,[status(esa)],[c_1221])).

cnf(c_2740,plain,
    ( k2_lattices(sK8,X0_60,X1_60) = k2_lattices(sK8,X1_60,X0_60)
    | m1_subset_1(X1_60,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2338])).

cnf(c_3350,plain,
    ( k2_lattices(sK8,X0_60,k15_lattice3(sK8,X0_63)) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),X0_60)
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2736,c_2740])).

cnf(c_4538,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,X0_60)) = k2_lattices(sK8,sK3(sK8,X0_60),k15_lattice3(sK8,X0_63))
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2745,c_3350])).

cnf(c_9645,plain,
    ( k2_lattices(sK8,sK3(sK8,sK3(sK8,X0_60)),k15_lattice3(sK8,X0_63)) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,X0_60)))
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2745,c_4538])).

cnf(c_18093,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))) = k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60))),k15_lattice3(sK8,X0_63))
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2745,c_9645])).

cnf(c_25948,plain,
    ( k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))),k15_lattice3(sK8,X0_63)) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))))
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2745,c_18093])).

cnf(c_40328,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))))) = k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60))))),k15_lattice3(sK8,X0_63))
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2745,c_25948])).

cnf(c_2356,plain,
    ( X0_63 != X1_63
    | k15_lattice3(X0_62,X0_63) = k15_lattice3(X0_62,X1_63) ),
    theory(equality)).

cnf(c_2361,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k15_lattice3(sK8,k1_xboole_0) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2356])).

cnf(c_2351,plain,
    ( X0_63 = X0_63 ),
    theory(equality)).

cnf(c_2365,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(c_36,negated_conjecture,
    ( ~ v13_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ v10_lattices(sK8)
    | k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_239,negated_conjecture,
    ( ~ v13_lattices(sK8)
    | k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_40,c_39,c_37])).

cnf(c_2348,negated_conjecture,
    ( ~ v13_lattices(sK8)
    | k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_239])).

cnf(c_2366,plain,
    ( k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0)
    | v13_lattices(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2348])).

cnf(c_2382,plain,
    ( m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2342])).

cnf(c_2384,plain,
    ( m1_subset_1(k15_lattice3(sK8,k1_xboole_0),u1_struct_0(sK8)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2382])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1343,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_40])).

cnf(c_1344,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8))
    | ~ l1_lattices(sK8)
    | ~ v13_lattices(sK8)
    | k2_lattices(sK8,X0,k5_lattices(sK8)) = k5_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_1343])).

cnf(c_16,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_104,plain,
    ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8))
    | ~ l1_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1348,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v13_lattices(sK8)
    | k2_lattices(sK8,X0,k5_lattices(sK8)) = k5_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1344,c_40,c_37,c_98,c_104])).

cnf(c_2330,plain,
    ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
    | ~ v13_lattices(sK8)
    | k2_lattices(sK8,X0_60,k5_lattices(sK8)) = k5_lattices(sK8) ),
    inference(subtyping,[status(esa)],[c_1348])).

cnf(c_2939,plain,
    ( ~ m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8))
    | ~ v13_lattices(sK8)
    | k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) = k5_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_2330])).

cnf(c_2940,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) = k5_lattices(sK8)
    | m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2939])).

cnf(c_2942,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) = k5_lattices(sK8)
    | m1_subset_1(k15_lattice3(sK8,k1_xboole_0),u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2940])).

cnf(c_2350,plain,
    ( X0_60 = X0_60 ),
    theory(equality)).

cnf(c_3185,plain,
    ( k5_lattices(sK8) = k5_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_2350])).

cnf(c_2352,plain,
    ( X0_60 != X1_60
    | X2_60 != X1_60
    | X2_60 = X0_60 ),
    theory(equality)).

cnf(c_2905,plain,
    ( X0_60 != X1_60
    | k5_lattices(sK8) != X1_60
    | k5_lattices(sK8) = X0_60 ),
    inference(instantiation,[status(thm)],[c_2352])).

cnf(c_3187,plain,
    ( X0_60 != k5_lattices(sK8)
    | k5_lattices(sK8) = X0_60
    | k5_lattices(sK8) != k5_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_2905])).

cnf(c_3801,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) != k5_lattices(sK8)
    | k5_lattices(sK8) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))
    | k5_lattices(sK8) != k5_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_3187])).

cnf(c_3807,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) != k5_lattices(sK8)
    | k5_lattices(sK8) = k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8))
    | k5_lattices(sK8) != k5_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_3801])).

cnf(c_2895,plain,
    ( k15_lattice3(sK8,k1_xboole_0) != X0_60
    | k5_lattices(sK8) != X0_60
    | k5_lattices(sK8) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2352])).

cnf(c_5333,plain,
    ( k15_lattice3(sK8,k1_xboole_0) != k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))
    | k5_lattices(sK8) != k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))
    | k5_lattices(sK8) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2895])).

cnf(c_5334,plain,
    ( k15_lattice3(sK8,k1_xboole_0) != k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8))
    | k5_lattices(sK8) != k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8))
    | k5_lattices(sK8) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5333])).

cnf(c_7784,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) != X0_60
    | k15_lattice3(sK8,k1_xboole_0) != X0_60
    | k15_lattice3(sK8,k1_xboole_0) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) ),
    inference(instantiation,[status(thm)],[c_2352])).

cnf(c_28233,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) != k15_lattice3(sK8,k1_xboole_0)
    | k15_lattice3(sK8,k1_xboole_0) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))
    | k15_lattice3(sK8,k1_xboole_0) != k15_lattice3(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7784])).

cnf(c_28234,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) != k15_lattice3(sK8,k1_xboole_0)
    | k15_lattice3(sK8,k1_xboole_0) = k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8))
    | k15_lattice3(sK8,k1_xboole_0) != k15_lattice3(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_28233])).

cnf(c_1206,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_40])).

cnf(c_1207,plain,
    ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8))
    | ~ l1_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_1206])).

cnf(c_1209,plain,
    ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1207,c_40,c_37,c_98,c_104])).

cnf(c_2336,plain,
    ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1209])).

cnf(c_2742,plain,
    ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2336])).

cnf(c_2947,plain,
    ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),k5_lattices(sK8))) = k5_lattices(sK8) ),
    inference(superposition,[status(thm)],[c_2742,c_2732])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_460,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_461,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_34,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK7(X0,X1,X2),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_697,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK7(X0,X1,X2),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_38])).

cnf(c_698,plain,
    ( r3_lattices(sK8,k15_lattice3(sK8,X0),k15_lattice3(sK8,X1))
    | r2_hidden(sK7(sK8,X0,X1),X0)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ v10_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_702,plain,
    ( r2_hidden(sK7(sK8,X0,X1),X0)
    | r3_lattices(sK8,k15_lattice3(sK8,X0),k15_lattice3(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_40,c_39,c_37])).

cnf(c_703,plain,
    ( r3_lattices(sK8,k15_lattice3(sK8,X0),k15_lattice3(sK8,X1))
    | r2_hidden(sK7(sK8,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_702])).

cnf(c_812,plain,
    ( r3_lattices(sK8,k15_lattice3(sK8,X0),k15_lattice3(sK8,X1))
    | sK7(sK8,X0,X1) != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_461,c_703])).

cnf(c_813,plain,
    ( r3_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0)) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_2343,plain,
    ( r3_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) ),
    inference(subtyping,[status(esa)],[c_813])).

cnf(c_2735,plain,
    ( r3_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2343])).

cnf(c_3,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_20,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_599,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0) ),
    inference(resolution,[status(thm)],[c_3,c_20])).

cnf(c_2,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_603,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_20,c_4,c_3,c_2])).

cnf(c_604,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_603])).

cnf(c_851,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_604,c_39])).

cnf(c_852,plain,
    ( ~ r3_lattices(sK8,X0,X1)
    | r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_851])).

cnf(c_856,plain,
    ( ~ r3_lattices(sK8,X0,X1)
    | r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_852,c_40,c_37])).

cnf(c_857,plain,
    ( ~ r3_lattices(sK8,X0,X1)
    | r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_856])).

cnf(c_17,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_11,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_471,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(resolution,[status(thm)],[c_17,c_11])).

cnf(c_935,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_471,c_37])).

cnf(c_936,plain,
    ( ~ r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | k1_lattices(sK8,X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_940,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r1_lattices(sK8,X0,X1)
    | k1_lattices(sK8,X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_40])).

cnf(c_941,plain,
    ( ~ r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k1_lattices(sK8,X0,X1) = X1 ),
    inference(renaming,[status(thm)],[c_940])).

cnf(c_1044,plain,
    ( ~ r3_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k1_lattices(sK8,X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_857,c_941])).

cnf(c_2339,plain,
    ( ~ r3_lattices(sK8,X0_60,X1_60)
    | ~ m1_subset_1(X0_60,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_60,u1_struct_0(sK8))
    | k1_lattices(sK8,X0_60,X1_60) = X1_60 ),
    inference(subtyping,[status(esa)],[c_1044])).

cnf(c_2739,plain,
    ( k1_lattices(sK8,X0_60,X1_60) = X1_60
    | r3_lattices(sK8,X0_60,X1_60) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_60,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2339])).

cnf(c_4939,plain,
    ( k1_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) = k15_lattice3(sK8,X0_63)
    | m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k15_lattice3(sK8,k1_xboole_0),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2735,c_2739])).

cnf(c_16250,plain,
    ( k1_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) = k15_lattice3(sK8,X0_63) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4939,c_2382,c_2384])).

cnf(c_16253,plain,
    ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),k5_lattices(sK8))) = k1_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) ),
    inference(superposition,[status(thm)],[c_2947,c_16250])).

cnf(c_16258,plain,
    ( k1_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) = k5_lattices(sK8) ),
    inference(light_normalisation,[status(thm)],[c_16253,c_2947])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_987,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_37])).

cnf(c_988,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | ~ v9_lattices(sK8)
    | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_144,plain,
    ( ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ v10_lattices(sK8)
    | v9_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_992,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_40,c_39,c_37,c_144])).

cnf(c_2341,plain,
    ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_60,u1_struct_0(sK8))
    | k2_lattices(sK8,X1_60,k1_lattices(sK8,X1_60,X0_60)) = X1_60 ),
    inference(subtyping,[status(esa)],[c_992])).

cnf(c_2737,plain,
    ( k2_lattices(sK8,X0_60,k1_lattices(sK8,X0_60,X1_60)) = X0_60
    | m1_subset_1(X1_60,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2341])).

cnf(c_3260,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k1_lattices(sK8,k15_lattice3(sK8,X0_63),X0_60)) = k15_lattice3(sK8,X0_63)
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2736,c_2737])).

cnf(c_4923,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k1_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))) = k15_lattice3(sK8,X0_63) ),
    inference(superposition,[status(thm)],[c_2742,c_3260])).

cnf(c_59067,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_16258,c_4923])).

cnf(c_59081,plain,
    ( m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
    | k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))))) = k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60))))),k15_lattice3(sK8,X0_63)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40328,c_2361,c_2365,c_2366,c_2384,c_2942,c_3185,c_3807,c_5334,c_28234,c_59067])).

cnf(c_59082,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))))) = k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60))))),k15_lattice3(sK8,X0_63))
    | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_59081])).

cnf(c_59087,plain,
    ( k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK4(sK8)))))),k15_lattice3(sK8,X0_63)) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK4(sK8)))))))
    | v13_lattices(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2741,c_59082])).

cnf(c_59369,plain,
    ( v13_lattices(sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_59087,c_2361,c_2365,c_2366,c_2384,c_2942,c_3185,c_3807,c_5334,c_28234,c_59067])).

cnf(c_59507,plain,
    ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK3(sK8,k15_lattice3(sK8,X0_63)))) = sK3(sK8,k15_lattice3(sK8,X0_63)) ),
    inference(superposition,[status(thm)],[c_6352,c_59369])).

cnf(c_4926,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k1_lattices(sK8,k15_lattice3(sK8,X0_63),k15_lattice3(sK8,X1_63))) = k15_lattice3(sK8,X0_63) ),
    inference(superposition,[status(thm)],[c_2736,c_3260])).

cnf(c_16256,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_16250,c_4926])).

cnf(c_65220,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),sK3(sK8,k15_lattice3(sK8,X0_63))) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_59507,c_16256])).

cnf(c_65368,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),sK3(sK8,k15_lattice3(sK8,k1_xboole_0))) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_65220])).

cnf(c_4539,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k15_lattice3(sK8,X1_63)) = k2_lattices(sK8,k15_lattice3(sK8,X1_63),k15_lattice3(sK8,X0_63)) ),
    inference(superposition,[status(thm)],[c_2736,c_3350])).

cnf(c_61432,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k15_lattice3(sK8,k1_xboole_0)) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_16256,c_4539])).

cnf(c_65208,plain,
    ( k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,X0_63)),k15_lattice3(sK8,k1_xboole_0)) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_59507,c_61432])).

cnf(c_65367,plain,
    ( k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,k1_xboole_0)),k15_lattice3(sK8,k1_xboole_0)) = k15_lattice3(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_65208])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK3(X1,X0)) != X0
    | k2_lattices(X1,sK3(X1,X0),X0) != X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1298,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | k2_lattices(X1,X0,sK3(X1,X0)) != X0
    | k2_lattices(X1,sK3(X1,X0),X0) != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_40])).

cnf(c_1299,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ l1_lattices(sK8)
    | v13_lattices(sK8)
    | k2_lattices(sK8,X0,sK3(sK8,X0)) != X0
    | k2_lattices(sK8,sK3(sK8,X0),X0) != X0 ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_1303,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v13_lattices(sK8)
    | k2_lattices(sK8,X0,sK3(sK8,X0)) != X0
    | k2_lattices(sK8,sK3(sK8,X0),X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1299,c_37,c_98])).

cnf(c_2332,plain,
    ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
    | v13_lattices(sK8)
    | k2_lattices(sK8,X0_60,sK3(sK8,X0_60)) != X0_60
    | k2_lattices(sK8,sK3(sK8,X0_60),X0_60) != X0_60 ),
    inference(subtyping,[status(esa)],[c_1303])).

cnf(c_2838,plain,
    ( ~ m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8))
    | v13_lattices(sK8)
    | k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,k15_lattice3(sK8,X0_63))) != k15_lattice3(sK8,X0_63)
    | k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,X0_63)),k15_lattice3(sK8,X0_63)) != k15_lattice3(sK8,X0_63) ),
    inference(instantiation,[status(thm)],[c_2332])).

cnf(c_2839,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,k15_lattice3(sK8,X0_63))) != k15_lattice3(sK8,X0_63)
    | k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,X0_63)),k15_lattice3(sK8,X0_63)) != k15_lattice3(sK8,X0_63)
    | m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2838])).

cnf(c_2841,plain,
    ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),sK3(sK8,k15_lattice3(sK8,k1_xboole_0))) != k15_lattice3(sK8,k1_xboole_0)
    | k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,k1_xboole_0)),k15_lattice3(sK8,k1_xboole_0)) != k15_lattice3(sK8,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK8,k1_xboole_0),u1_struct_0(sK8)) != iProver_top
    | v13_lattices(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2839])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65368,c_65367,c_59369,c_2841,c_2384])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:29:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.54/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.54/3.49  
% 23.54/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.54/3.49  
% 23.54/3.49  ------  iProver source info
% 23.54/3.49  
% 23.54/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.54/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.54/3.49  git: non_committed_changes: false
% 23.54/3.49  git: last_make_outside_of_git: false
% 23.54/3.49  
% 23.54/3.49  ------ 
% 23.54/3.49  
% 23.54/3.49  ------ Input Options
% 23.54/3.49  
% 23.54/3.49  --out_options                           all
% 23.54/3.49  --tptp_safe_out                         true
% 23.54/3.49  --problem_path                          ""
% 23.54/3.49  --include_path                          ""
% 23.54/3.49  --clausifier                            res/vclausify_rel
% 23.54/3.49  --clausifier_options                    ""
% 23.54/3.49  --stdin                                 false
% 23.54/3.49  --stats_out                             all
% 23.54/3.49  
% 23.54/3.49  ------ General Options
% 23.54/3.49  
% 23.54/3.49  --fof                                   false
% 23.54/3.49  --time_out_real                         305.
% 23.54/3.49  --time_out_virtual                      -1.
% 23.54/3.49  --symbol_type_check                     false
% 23.54/3.49  --clausify_out                          false
% 23.54/3.49  --sig_cnt_out                           false
% 23.54/3.49  --trig_cnt_out                          false
% 23.54/3.49  --trig_cnt_out_tolerance                1.
% 23.54/3.49  --trig_cnt_out_sk_spl                   false
% 23.54/3.49  --abstr_cl_out                          false
% 23.54/3.49  
% 23.54/3.49  ------ Global Options
% 23.54/3.49  
% 23.54/3.49  --schedule                              default
% 23.54/3.49  --add_important_lit                     false
% 23.54/3.49  --prop_solver_per_cl                    1000
% 23.54/3.49  --min_unsat_core                        false
% 23.54/3.49  --soft_assumptions                      false
% 23.54/3.49  --soft_lemma_size                       3
% 23.54/3.49  --prop_impl_unit_size                   0
% 23.54/3.49  --prop_impl_unit                        []
% 23.54/3.49  --share_sel_clauses                     true
% 23.54/3.49  --reset_solvers                         false
% 23.54/3.49  --bc_imp_inh                            [conj_cone]
% 23.54/3.49  --conj_cone_tolerance                   3.
% 23.54/3.49  --extra_neg_conj                        none
% 23.54/3.49  --large_theory_mode                     true
% 23.54/3.49  --prolific_symb_bound                   200
% 23.54/3.49  --lt_threshold                          2000
% 23.54/3.49  --clause_weak_htbl                      true
% 23.54/3.49  --gc_record_bc_elim                     false
% 23.54/3.49  
% 23.54/3.49  ------ Preprocessing Options
% 23.54/3.49  
% 23.54/3.49  --preprocessing_flag                    true
% 23.54/3.49  --time_out_prep_mult                    0.1
% 23.54/3.49  --splitting_mode                        input
% 23.54/3.49  --splitting_grd                         true
% 23.54/3.49  --splitting_cvd                         false
% 23.54/3.49  --splitting_cvd_svl                     false
% 23.54/3.49  --splitting_nvd                         32
% 23.54/3.49  --sub_typing                            true
% 23.54/3.49  --prep_gs_sim                           true
% 23.54/3.49  --prep_unflatten                        true
% 23.54/3.49  --prep_res_sim                          true
% 23.54/3.49  --prep_upred                            true
% 23.54/3.49  --prep_sem_filter                       exhaustive
% 23.54/3.49  --prep_sem_filter_out                   false
% 23.54/3.49  --pred_elim                             true
% 23.54/3.49  --res_sim_input                         true
% 23.54/3.49  --eq_ax_congr_red                       true
% 23.54/3.49  --pure_diseq_elim                       true
% 23.54/3.49  --brand_transform                       false
% 23.54/3.49  --non_eq_to_eq                          false
% 23.54/3.49  --prep_def_merge                        true
% 23.54/3.49  --prep_def_merge_prop_impl              false
% 23.54/3.49  --prep_def_merge_mbd                    true
% 23.54/3.49  --prep_def_merge_tr_red                 false
% 23.54/3.49  --prep_def_merge_tr_cl                  false
% 23.54/3.49  --smt_preprocessing                     true
% 23.54/3.49  --smt_ac_axioms                         fast
% 23.54/3.49  --preprocessed_out                      false
% 23.54/3.49  --preprocessed_stats                    false
% 23.54/3.49  
% 23.54/3.49  ------ Abstraction refinement Options
% 23.54/3.49  
% 23.54/3.49  --abstr_ref                             []
% 23.54/3.49  --abstr_ref_prep                        false
% 23.54/3.49  --abstr_ref_until_sat                   false
% 23.54/3.49  --abstr_ref_sig_restrict                funpre
% 23.54/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.54/3.49  --abstr_ref_under                       []
% 23.54/3.49  
% 23.54/3.49  ------ SAT Options
% 23.54/3.49  
% 23.54/3.49  --sat_mode                              false
% 23.54/3.49  --sat_fm_restart_options                ""
% 23.54/3.49  --sat_gr_def                            false
% 23.54/3.49  --sat_epr_types                         true
% 23.54/3.49  --sat_non_cyclic_types                  false
% 23.54/3.49  --sat_finite_models                     false
% 23.54/3.49  --sat_fm_lemmas                         false
% 23.54/3.49  --sat_fm_prep                           false
% 23.54/3.49  --sat_fm_uc_incr                        true
% 23.54/3.49  --sat_out_model                         small
% 23.54/3.49  --sat_out_clauses                       false
% 23.54/3.49  
% 23.54/3.49  ------ QBF Options
% 23.54/3.49  
% 23.54/3.49  --qbf_mode                              false
% 23.54/3.49  --qbf_elim_univ                         false
% 23.54/3.49  --qbf_dom_inst                          none
% 23.54/3.49  --qbf_dom_pre_inst                      false
% 23.54/3.49  --qbf_sk_in                             false
% 23.54/3.49  --qbf_pred_elim                         true
% 23.54/3.49  --qbf_split                             512
% 23.54/3.49  
% 23.54/3.49  ------ BMC1 Options
% 23.54/3.49  
% 23.54/3.49  --bmc1_incremental                      false
% 23.54/3.49  --bmc1_axioms                           reachable_all
% 23.54/3.49  --bmc1_min_bound                        0
% 23.54/3.49  --bmc1_max_bound                        -1
% 23.54/3.49  --bmc1_max_bound_default                -1
% 23.54/3.49  --bmc1_symbol_reachability              true
% 23.54/3.49  --bmc1_property_lemmas                  false
% 23.54/3.49  --bmc1_k_induction                      false
% 23.54/3.49  --bmc1_non_equiv_states                 false
% 23.54/3.49  --bmc1_deadlock                         false
% 23.54/3.49  --bmc1_ucm                              false
% 23.54/3.49  --bmc1_add_unsat_core                   none
% 23.54/3.49  --bmc1_unsat_core_children              false
% 23.54/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.54/3.49  --bmc1_out_stat                         full
% 23.54/3.49  --bmc1_ground_init                      false
% 23.54/3.49  --bmc1_pre_inst_next_state              false
% 23.54/3.49  --bmc1_pre_inst_state                   false
% 23.54/3.49  --bmc1_pre_inst_reach_state             false
% 23.54/3.49  --bmc1_out_unsat_core                   false
% 23.54/3.49  --bmc1_aig_witness_out                  false
% 23.54/3.49  --bmc1_verbose                          false
% 23.54/3.49  --bmc1_dump_clauses_tptp                false
% 23.54/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.54/3.49  --bmc1_dump_file                        -
% 23.54/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.54/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.54/3.49  --bmc1_ucm_extend_mode                  1
% 23.54/3.49  --bmc1_ucm_init_mode                    2
% 23.54/3.49  --bmc1_ucm_cone_mode                    none
% 23.54/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.54/3.49  --bmc1_ucm_relax_model                  4
% 23.54/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.54/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.54/3.49  --bmc1_ucm_layered_model                none
% 23.54/3.49  --bmc1_ucm_max_lemma_size               10
% 23.54/3.49  
% 23.54/3.49  ------ AIG Options
% 23.54/3.49  
% 23.54/3.49  --aig_mode                              false
% 23.54/3.49  
% 23.54/3.49  ------ Instantiation Options
% 23.54/3.49  
% 23.54/3.49  --instantiation_flag                    true
% 23.54/3.49  --inst_sos_flag                         true
% 23.54/3.49  --inst_sos_phase                        true
% 23.54/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.54/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.54/3.49  --inst_lit_sel_side                     num_symb
% 23.54/3.49  --inst_solver_per_active                1400
% 23.54/3.49  --inst_solver_calls_frac                1.
% 23.54/3.49  --inst_passive_queue_type               priority_queues
% 23.54/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.54/3.49  --inst_passive_queues_freq              [25;2]
% 23.54/3.49  --inst_dismatching                      true
% 23.54/3.49  --inst_eager_unprocessed_to_passive     true
% 23.54/3.49  --inst_prop_sim_given                   true
% 23.54/3.49  --inst_prop_sim_new                     false
% 23.54/3.49  --inst_subs_new                         false
% 23.54/3.49  --inst_eq_res_simp                      false
% 23.54/3.49  --inst_subs_given                       false
% 23.54/3.49  --inst_orphan_elimination               true
% 23.54/3.49  --inst_learning_loop_flag               true
% 23.54/3.49  --inst_learning_start                   3000
% 23.54/3.49  --inst_learning_factor                  2
% 23.54/3.49  --inst_start_prop_sim_after_learn       3
% 23.54/3.49  --inst_sel_renew                        solver
% 23.54/3.49  --inst_lit_activity_flag                true
% 23.54/3.49  --inst_restr_to_given                   false
% 23.54/3.49  --inst_activity_threshold               500
% 23.54/3.49  --inst_out_proof                        true
% 23.54/3.49  
% 23.54/3.49  ------ Resolution Options
% 23.54/3.49  
% 23.54/3.49  --resolution_flag                       true
% 23.54/3.49  --res_lit_sel                           adaptive
% 23.54/3.49  --res_lit_sel_side                      none
% 23.54/3.49  --res_ordering                          kbo
% 23.54/3.49  --res_to_prop_solver                    active
% 23.54/3.49  --res_prop_simpl_new                    false
% 23.54/3.49  --res_prop_simpl_given                  true
% 23.54/3.49  --res_passive_queue_type                priority_queues
% 23.54/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.54/3.49  --res_passive_queues_freq               [15;5]
% 23.54/3.49  --res_forward_subs                      full
% 23.54/3.49  --res_backward_subs                     full
% 23.54/3.49  --res_forward_subs_resolution           true
% 23.54/3.49  --res_backward_subs_resolution          true
% 23.54/3.49  --res_orphan_elimination                true
% 23.54/3.49  --res_time_limit                        2.
% 23.54/3.49  --res_out_proof                         true
% 23.54/3.49  
% 23.54/3.49  ------ Superposition Options
% 23.54/3.49  
% 23.54/3.49  --superposition_flag                    true
% 23.54/3.49  --sup_passive_queue_type                priority_queues
% 23.54/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.54/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.54/3.49  --demod_completeness_check              fast
% 23.54/3.49  --demod_use_ground                      true
% 23.54/3.49  --sup_to_prop_solver                    passive
% 23.54/3.49  --sup_prop_simpl_new                    true
% 23.54/3.49  --sup_prop_simpl_given                  true
% 23.54/3.49  --sup_fun_splitting                     true
% 23.54/3.49  --sup_smt_interval                      50000
% 23.54/3.50  
% 23.54/3.50  ------ Superposition Simplification Setup
% 23.54/3.50  
% 23.54/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.54/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.54/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.54/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.54/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.54/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.54/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.54/3.50  --sup_immed_triv                        [TrivRules]
% 23.54/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_immed_bw_main                     []
% 23.54/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.54/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.54/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_input_bw                          []
% 23.54/3.50  
% 23.54/3.50  ------ Combination Options
% 23.54/3.50  
% 23.54/3.50  --comb_res_mult                         3
% 23.54/3.50  --comb_sup_mult                         2
% 23.54/3.50  --comb_inst_mult                        10
% 23.54/3.50  
% 23.54/3.50  ------ Debug Options
% 23.54/3.50  
% 23.54/3.50  --dbg_backtrace                         false
% 23.54/3.50  --dbg_dump_prop_clauses                 false
% 23.54/3.50  --dbg_dump_prop_clauses_file            -
% 23.54/3.50  --dbg_out_stat                          false
% 23.54/3.50  ------ Parsing...
% 23.54/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.54/3.50  ------ Proving...
% 23.54/3.50  ------ Problem Properties 
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  clauses                                 21
% 23.54/3.50  conjectures                             1
% 23.54/3.50  EPR                                     0
% 23.54/3.50  Horn                                    17
% 23.54/3.50  unary                                   3
% 23.54/3.50  binary                                  5
% 23.54/3.50  lits                                    58
% 23.54/3.50  lits eq                                 17
% 23.54/3.50  fd_pure                                 0
% 23.54/3.50  fd_pseudo                               0
% 23.54/3.50  fd_cond                                 2
% 23.54/3.50  fd_pseudo_cond                          0
% 23.54/3.50  AC symbols                              0
% 23.54/3.50  
% 23.54/3.50  ------ Schedule dynamic 5 is on 
% 23.54/3.50  
% 23.54/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  ------ 
% 23.54/3.50  Current options:
% 23.54/3.50  ------ 
% 23.54/3.50  
% 23.54/3.50  ------ Input Options
% 23.54/3.50  
% 23.54/3.50  --out_options                           all
% 23.54/3.50  --tptp_safe_out                         true
% 23.54/3.50  --problem_path                          ""
% 23.54/3.50  --include_path                          ""
% 23.54/3.50  --clausifier                            res/vclausify_rel
% 23.54/3.50  --clausifier_options                    ""
% 23.54/3.50  --stdin                                 false
% 23.54/3.50  --stats_out                             all
% 23.54/3.50  
% 23.54/3.50  ------ General Options
% 23.54/3.50  
% 23.54/3.50  --fof                                   false
% 23.54/3.50  --time_out_real                         305.
% 23.54/3.50  --time_out_virtual                      -1.
% 23.54/3.50  --symbol_type_check                     false
% 23.54/3.50  --clausify_out                          false
% 23.54/3.50  --sig_cnt_out                           false
% 23.54/3.50  --trig_cnt_out                          false
% 23.54/3.50  --trig_cnt_out_tolerance                1.
% 23.54/3.50  --trig_cnt_out_sk_spl                   false
% 23.54/3.50  --abstr_cl_out                          false
% 23.54/3.50  
% 23.54/3.50  ------ Global Options
% 23.54/3.50  
% 23.54/3.50  --schedule                              default
% 23.54/3.50  --add_important_lit                     false
% 23.54/3.50  --prop_solver_per_cl                    1000
% 23.54/3.50  --min_unsat_core                        false
% 23.54/3.50  --soft_assumptions                      false
% 23.54/3.50  --soft_lemma_size                       3
% 23.54/3.50  --prop_impl_unit_size                   0
% 23.54/3.50  --prop_impl_unit                        []
% 23.54/3.50  --share_sel_clauses                     true
% 23.54/3.50  --reset_solvers                         false
% 23.54/3.50  --bc_imp_inh                            [conj_cone]
% 23.54/3.50  --conj_cone_tolerance                   3.
% 23.54/3.50  --extra_neg_conj                        none
% 23.54/3.50  --large_theory_mode                     true
% 23.54/3.50  --prolific_symb_bound                   200
% 23.54/3.50  --lt_threshold                          2000
% 23.54/3.50  --clause_weak_htbl                      true
% 23.54/3.50  --gc_record_bc_elim                     false
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing Options
% 23.54/3.50  
% 23.54/3.50  --preprocessing_flag                    true
% 23.54/3.50  --time_out_prep_mult                    0.1
% 23.54/3.50  --splitting_mode                        input
% 23.54/3.50  --splitting_grd                         true
% 23.54/3.50  --splitting_cvd                         false
% 23.54/3.50  --splitting_cvd_svl                     false
% 23.54/3.50  --splitting_nvd                         32
% 23.54/3.50  --sub_typing                            true
% 23.54/3.50  --prep_gs_sim                           true
% 23.54/3.50  --prep_unflatten                        true
% 23.54/3.50  --prep_res_sim                          true
% 23.54/3.50  --prep_upred                            true
% 23.54/3.50  --prep_sem_filter                       exhaustive
% 23.54/3.50  --prep_sem_filter_out                   false
% 23.54/3.50  --pred_elim                             true
% 23.54/3.50  --res_sim_input                         true
% 23.54/3.50  --eq_ax_congr_red                       true
% 23.54/3.50  --pure_diseq_elim                       true
% 23.54/3.50  --brand_transform                       false
% 23.54/3.50  --non_eq_to_eq                          false
% 23.54/3.50  --prep_def_merge                        true
% 23.54/3.50  --prep_def_merge_prop_impl              false
% 23.54/3.50  --prep_def_merge_mbd                    true
% 23.54/3.50  --prep_def_merge_tr_red                 false
% 23.54/3.50  --prep_def_merge_tr_cl                  false
% 23.54/3.50  --smt_preprocessing                     true
% 23.54/3.50  --smt_ac_axioms                         fast
% 23.54/3.50  --preprocessed_out                      false
% 23.54/3.50  --preprocessed_stats                    false
% 23.54/3.50  
% 23.54/3.50  ------ Abstraction refinement Options
% 23.54/3.50  
% 23.54/3.50  --abstr_ref                             []
% 23.54/3.50  --abstr_ref_prep                        false
% 23.54/3.50  --abstr_ref_until_sat                   false
% 23.54/3.50  --abstr_ref_sig_restrict                funpre
% 23.54/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.54/3.50  --abstr_ref_under                       []
% 23.54/3.50  
% 23.54/3.50  ------ SAT Options
% 23.54/3.50  
% 23.54/3.50  --sat_mode                              false
% 23.54/3.50  --sat_fm_restart_options                ""
% 23.54/3.50  --sat_gr_def                            false
% 23.54/3.50  --sat_epr_types                         true
% 23.54/3.50  --sat_non_cyclic_types                  false
% 23.54/3.50  --sat_finite_models                     false
% 23.54/3.50  --sat_fm_lemmas                         false
% 23.54/3.50  --sat_fm_prep                           false
% 23.54/3.50  --sat_fm_uc_incr                        true
% 23.54/3.50  --sat_out_model                         small
% 23.54/3.50  --sat_out_clauses                       false
% 23.54/3.50  
% 23.54/3.50  ------ QBF Options
% 23.54/3.50  
% 23.54/3.50  --qbf_mode                              false
% 23.54/3.50  --qbf_elim_univ                         false
% 23.54/3.50  --qbf_dom_inst                          none
% 23.54/3.50  --qbf_dom_pre_inst                      false
% 23.54/3.50  --qbf_sk_in                             false
% 23.54/3.50  --qbf_pred_elim                         true
% 23.54/3.50  --qbf_split                             512
% 23.54/3.50  
% 23.54/3.50  ------ BMC1 Options
% 23.54/3.50  
% 23.54/3.50  --bmc1_incremental                      false
% 23.54/3.50  --bmc1_axioms                           reachable_all
% 23.54/3.50  --bmc1_min_bound                        0
% 23.54/3.50  --bmc1_max_bound                        -1
% 23.54/3.50  --bmc1_max_bound_default                -1
% 23.54/3.50  --bmc1_symbol_reachability              true
% 23.54/3.50  --bmc1_property_lemmas                  false
% 23.54/3.50  --bmc1_k_induction                      false
% 23.54/3.50  --bmc1_non_equiv_states                 false
% 23.54/3.50  --bmc1_deadlock                         false
% 23.54/3.50  --bmc1_ucm                              false
% 23.54/3.50  --bmc1_add_unsat_core                   none
% 23.54/3.50  --bmc1_unsat_core_children              false
% 23.54/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.54/3.50  --bmc1_out_stat                         full
% 23.54/3.50  --bmc1_ground_init                      false
% 23.54/3.50  --bmc1_pre_inst_next_state              false
% 23.54/3.50  --bmc1_pre_inst_state                   false
% 23.54/3.50  --bmc1_pre_inst_reach_state             false
% 23.54/3.50  --bmc1_out_unsat_core                   false
% 23.54/3.50  --bmc1_aig_witness_out                  false
% 23.54/3.50  --bmc1_verbose                          false
% 23.54/3.50  --bmc1_dump_clauses_tptp                false
% 23.54/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.54/3.50  --bmc1_dump_file                        -
% 23.54/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.54/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.54/3.50  --bmc1_ucm_extend_mode                  1
% 23.54/3.50  --bmc1_ucm_init_mode                    2
% 23.54/3.50  --bmc1_ucm_cone_mode                    none
% 23.54/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.54/3.50  --bmc1_ucm_relax_model                  4
% 23.54/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.54/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.54/3.50  --bmc1_ucm_layered_model                none
% 23.54/3.50  --bmc1_ucm_max_lemma_size               10
% 23.54/3.50  
% 23.54/3.50  ------ AIG Options
% 23.54/3.50  
% 23.54/3.50  --aig_mode                              false
% 23.54/3.50  
% 23.54/3.50  ------ Instantiation Options
% 23.54/3.50  
% 23.54/3.50  --instantiation_flag                    true
% 23.54/3.50  --inst_sos_flag                         true
% 23.54/3.50  --inst_sos_phase                        true
% 23.54/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.54/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.54/3.50  --inst_lit_sel_side                     none
% 23.54/3.50  --inst_solver_per_active                1400
% 23.54/3.50  --inst_solver_calls_frac                1.
% 23.54/3.50  --inst_passive_queue_type               priority_queues
% 23.54/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.54/3.50  --inst_passive_queues_freq              [25;2]
% 23.54/3.50  --inst_dismatching                      true
% 23.54/3.50  --inst_eager_unprocessed_to_passive     true
% 23.54/3.50  --inst_prop_sim_given                   true
% 23.54/3.50  --inst_prop_sim_new                     false
% 23.54/3.50  --inst_subs_new                         false
% 23.54/3.50  --inst_eq_res_simp                      false
% 23.54/3.50  --inst_subs_given                       false
% 23.54/3.50  --inst_orphan_elimination               true
% 23.54/3.50  --inst_learning_loop_flag               true
% 23.54/3.50  --inst_learning_start                   3000
% 23.54/3.50  --inst_learning_factor                  2
% 23.54/3.50  --inst_start_prop_sim_after_learn       3
% 23.54/3.50  --inst_sel_renew                        solver
% 23.54/3.50  --inst_lit_activity_flag                true
% 23.54/3.50  --inst_restr_to_given                   false
% 23.54/3.50  --inst_activity_threshold               500
% 23.54/3.50  --inst_out_proof                        true
% 23.54/3.50  
% 23.54/3.50  ------ Resolution Options
% 23.54/3.50  
% 23.54/3.50  --resolution_flag                       false
% 23.54/3.50  --res_lit_sel                           adaptive
% 23.54/3.50  --res_lit_sel_side                      none
% 23.54/3.50  --res_ordering                          kbo
% 23.54/3.50  --res_to_prop_solver                    active
% 23.54/3.50  --res_prop_simpl_new                    false
% 23.54/3.50  --res_prop_simpl_given                  true
% 23.54/3.50  --res_passive_queue_type                priority_queues
% 23.54/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.54/3.50  --res_passive_queues_freq               [15;5]
% 23.54/3.50  --res_forward_subs                      full
% 23.54/3.50  --res_backward_subs                     full
% 23.54/3.50  --res_forward_subs_resolution           true
% 23.54/3.50  --res_backward_subs_resolution          true
% 23.54/3.50  --res_orphan_elimination                true
% 23.54/3.50  --res_time_limit                        2.
% 23.54/3.50  --res_out_proof                         true
% 23.54/3.50  
% 23.54/3.50  ------ Superposition Options
% 23.54/3.50  
% 23.54/3.50  --superposition_flag                    true
% 23.54/3.50  --sup_passive_queue_type                priority_queues
% 23.54/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.54/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.54/3.50  --demod_completeness_check              fast
% 23.54/3.50  --demod_use_ground                      true
% 23.54/3.50  --sup_to_prop_solver                    passive
% 23.54/3.50  --sup_prop_simpl_new                    true
% 23.54/3.50  --sup_prop_simpl_given                  true
% 23.54/3.50  --sup_fun_splitting                     true
% 23.54/3.50  --sup_smt_interval                      50000
% 23.54/3.50  
% 23.54/3.50  ------ Superposition Simplification Setup
% 23.54/3.50  
% 23.54/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.54/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.54/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.54/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.54/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.54/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.54/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.54/3.50  --sup_immed_triv                        [TrivRules]
% 23.54/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_immed_bw_main                     []
% 23.54/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.54/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.54/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.54/3.50  --sup_input_bw                          []
% 23.54/3.50  
% 23.54/3.50  ------ Combination Options
% 23.54/3.50  
% 23.54/3.50  --comb_res_mult                         3
% 23.54/3.50  --comb_sup_mult                         2
% 23.54/3.50  --comb_inst_mult                        10
% 23.54/3.50  
% 23.54/3.50  ------ Debug Options
% 23.54/3.50  
% 23.54/3.50  --dbg_backtrace                         false
% 23.54/3.50  --dbg_dump_prop_clauses                 false
% 23.54/3.50  --dbg_dump_prop_clauses_file            -
% 23.54/3.50  --dbg_out_stat                          false
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  ------ Proving...
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  % SZS status Theorem for theBenchmark.p
% 23.54/3.50  
% 23.54/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.54/3.50  
% 23.54/3.50  fof(f12,axiom,(
% 23.54/3.50    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f38,plain,(
% 23.54/3.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f12])).
% 23.54/3.50  
% 23.54/3.50  fof(f39,plain,(
% 23.54/3.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f38])).
% 23.54/3.50  
% 23.54/3.50  fof(f101,plain,(
% 23.54/3.50    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f39])).
% 23.54/3.50  
% 23.54/3.50  fof(f15,conjecture,(
% 23.54/3.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f16,negated_conjecture,(
% 23.54/3.50    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 23.54/3.50    inference(negated_conjecture,[],[f15])).
% 23.54/3.50  
% 23.54/3.50  fof(f44,plain,(
% 23.54/3.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f16])).
% 23.54/3.50  
% 23.54/3.50  fof(f45,plain,(
% 23.54/3.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f44])).
% 23.54/3.50  
% 23.54/3.50  fof(f69,plain,(
% 23.54/3.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0) | ~l3_lattices(sK8) | ~v13_lattices(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8)) & l3_lattices(sK8) & v4_lattice3(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f70,plain,(
% 23.54/3.50    (k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0) | ~l3_lattices(sK8) | ~v13_lattices(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8)) & l3_lattices(sK8) & v4_lattice3(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8)),
% 23.54/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f45,f69])).
% 23.54/3.50  
% 23.54/3.50  fof(f110,plain,(
% 23.54/3.50    l3_lattices(sK8)),
% 23.54/3.50    inference(cnf_transformation,[],[f70])).
% 23.54/3.50  
% 23.54/3.50  fof(f107,plain,(
% 23.54/3.50    ~v2_struct_0(sK8)),
% 23.54/3.50    inference(cnf_transformation,[],[f70])).
% 23.54/3.50  
% 23.54/3.50  fof(f10,axiom,(
% 23.54/3.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f34,plain,(
% 23.54/3.50    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f10])).
% 23.54/3.50  
% 23.54/3.50  fof(f35,plain,(
% 23.54/3.50    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f34])).
% 23.54/3.50  
% 23.54/3.50  fof(f57,plain,(
% 23.54/3.50    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(nnf_transformation,[],[f35])).
% 23.54/3.50  
% 23.54/3.50  fof(f58,plain,(
% 23.54/3.50    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(rectify,[],[f57])).
% 23.54/3.50  
% 23.54/3.50  fof(f60,plain,(
% 23.54/3.50    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((k2_lattices(X0,X4,sK4(X0)) = sK4(X0) & k2_lattices(X0,sK4(X0),X4) = sK4(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f59,plain,(
% 23.54/3.50    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f61,plain,(
% 23.54/3.50    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((k2_lattices(X0,X4,sK4(X0)) = sK4(X0) & k2_lattices(X0,sK4(X0),X4) = sK4(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f58,f60,f59])).
% 23.54/3.50  
% 23.54/3.50  fof(f95,plain,(
% 23.54/3.50    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f61])).
% 23.54/3.50  
% 23.54/3.50  fof(f8,axiom,(
% 23.54/3.50    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f31,plain,(
% 23.54/3.50    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 23.54/3.50    inference(ennf_transformation,[],[f8])).
% 23.54/3.50  
% 23.54/3.50  fof(f88,plain,(
% 23.54/3.50    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f31])).
% 23.54/3.50  
% 23.54/3.50  fof(f13,axiom,(
% 23.54/3.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f40,plain,(
% 23.54/3.50    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f13])).
% 23.54/3.50  
% 23.54/3.50  fof(f41,plain,(
% 23.54/3.50    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f40])).
% 23.54/3.50  
% 23.54/3.50  fof(f102,plain,(
% 23.54/3.50    ( ! [X0,X1] : (k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f41])).
% 23.54/3.50  
% 23.54/3.50  fof(f109,plain,(
% 23.54/3.50    v4_lattice3(sK8)),
% 23.54/3.50    inference(cnf_transformation,[],[f70])).
% 23.54/3.50  
% 23.54/3.50  fof(f108,plain,(
% 23.54/3.50    v10_lattices(sK8)),
% 23.54/3.50    inference(cnf_transformation,[],[f70])).
% 23.54/3.50  
% 23.54/3.50  fof(f92,plain,(
% 23.54/3.50    ( ! [X0] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f61])).
% 23.54/3.50  
% 23.54/3.50  fof(f11,axiom,(
% 23.54/3.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f36,plain,(
% 23.54/3.50    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f11])).
% 23.54/3.50  
% 23.54/3.50  fof(f37,plain,(
% 23.54/3.50    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f36])).
% 23.54/3.50  
% 23.54/3.50  fof(f62,plain,(
% 23.54/3.50    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(nnf_transformation,[],[f37])).
% 23.54/3.50  
% 23.54/3.50  fof(f63,plain,(
% 23.54/3.50    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(rectify,[],[f62])).
% 23.54/3.50  
% 23.54/3.50  fof(f65,plain,(
% 23.54/3.50    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK6(X0)) != k2_lattices(X0,sK6(X0),X1) & m1_subset_1(sK6(X0),u1_struct_0(X0))))) )),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f64,plain,(
% 23.54/3.50    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK5(X0)) != k2_lattices(X0,sK5(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f66,plain,(
% 23.54/3.50    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f63,f65,f64])).
% 23.54/3.50  
% 23.54/3.50  fof(f97,plain,(
% 23.54/3.50    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f66])).
% 23.54/3.50  
% 23.54/3.50  fof(f3,axiom,(
% 23.54/3.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f17,plain,(
% 23.54/3.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 23.54/3.50    inference(pure_predicate_removal,[],[f3])).
% 23.54/3.50  
% 23.54/3.50  fof(f18,plain,(
% 23.54/3.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 23.54/3.50    inference(pure_predicate_removal,[],[f17])).
% 23.54/3.50  
% 23.54/3.50  fof(f19,plain,(
% 23.54/3.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 23.54/3.50    inference(pure_predicate_removal,[],[f18])).
% 23.54/3.50  
% 23.54/3.50  fof(f21,plain,(
% 23.54/3.50    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 23.54/3.50    inference(ennf_transformation,[],[f19])).
% 23.54/3.50  
% 23.54/3.50  fof(f22,plain,(
% 23.54/3.50    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 23.54/3.50    inference(flattening,[],[f21])).
% 23.54/3.50  
% 23.54/3.50  fof(f74,plain,(
% 23.54/3.50    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f22])).
% 23.54/3.50  
% 23.54/3.50  fof(f111,plain,(
% 23.54/3.50    k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0) | ~l3_lattices(sK8) | ~v13_lattices(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8)),
% 23.54/3.50    inference(cnf_transformation,[],[f70])).
% 23.54/3.50  
% 23.54/3.50  fof(f4,axiom,(
% 23.54/3.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f23,plain,(
% 23.54/3.50    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f4])).
% 23.54/3.50  
% 23.54/3.50  fof(f24,plain,(
% 23.54/3.50    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f23])).
% 23.54/3.50  
% 23.54/3.50  fof(f46,plain,(
% 23.54/3.50    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(nnf_transformation,[],[f24])).
% 23.54/3.50  
% 23.54/3.50  fof(f47,plain,(
% 23.54/3.50    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(rectify,[],[f46])).
% 23.54/3.50  
% 23.54/3.50  fof(f48,plain,(
% 23.54/3.50    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f49,plain,(
% 23.54/3.50    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 23.54/3.50  
% 23.54/3.50  fof(f78,plain,(
% 23.54/3.50    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f49])).
% 23.54/3.50  
% 23.54/3.50  fof(f112,plain,(
% 23.54/3.50    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(equality_resolution,[],[f78])).
% 23.54/3.50  
% 23.54/3.50  fof(f7,axiom,(
% 23.54/3.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f29,plain,(
% 23.54/3.50    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f7])).
% 23.54/3.50  
% 23.54/3.50  fof(f30,plain,(
% 23.54/3.50    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f29])).
% 23.54/3.50  
% 23.54/3.50  fof(f87,plain,(
% 23.54/3.50    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f30])).
% 23.54/3.50  
% 23.54/3.50  fof(f1,axiom,(
% 23.54/3.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f71,plain,(
% 23.54/3.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f1])).
% 23.54/3.50  
% 23.54/3.50  fof(f2,axiom,(
% 23.54/3.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f20,plain,(
% 23.54/3.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 23.54/3.50    inference(ennf_transformation,[],[f2])).
% 23.54/3.50  
% 23.54/3.50  fof(f72,plain,(
% 23.54/3.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f20])).
% 23.54/3.50  
% 23.54/3.50  fof(f14,axiom,(
% 23.54/3.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f42,plain,(
% 23.54/3.50    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f14])).
% 23.54/3.50  
% 23.54/3.50  fof(f43,plain,(
% 23.54/3.50    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f42])).
% 23.54/3.50  
% 23.54/3.50  fof(f67,plain,(
% 23.54/3.50    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK7(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f68,plain,(
% 23.54/3.50    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK7(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f67])).
% 23.54/3.50  
% 23.54/3.50  fof(f105,plain,(
% 23.54/3.50    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | r2_hidden(sK7(X0,X1,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f68])).
% 23.54/3.50  
% 23.54/3.50  fof(f75,plain,(
% 23.54/3.50    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f22])).
% 23.54/3.50  
% 23.54/3.50  fof(f9,axiom,(
% 23.54/3.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f32,plain,(
% 23.54/3.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f9])).
% 23.54/3.50  
% 23.54/3.50  fof(f33,plain,(
% 23.54/3.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f32])).
% 23.54/3.50  
% 23.54/3.50  fof(f56,plain,(
% 23.54/3.50    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(nnf_transformation,[],[f33])).
% 23.54/3.50  
% 23.54/3.50  fof(f90,plain,(
% 23.54/3.50    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f56])).
% 23.54/3.50  
% 23.54/3.50  fof(f76,plain,(
% 23.54/3.50    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f22])).
% 23.54/3.50  
% 23.54/3.50  fof(f89,plain,(
% 23.54/3.50    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f31])).
% 23.54/3.50  
% 23.54/3.50  fof(f5,axiom,(
% 23.54/3.50    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f25,plain,(
% 23.54/3.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f5])).
% 23.54/3.50  
% 23.54/3.50  fof(f26,plain,(
% 23.54/3.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f25])).
% 23.54/3.50  
% 23.54/3.50  fof(f50,plain,(
% 23.54/3.50    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(nnf_transformation,[],[f26])).
% 23.54/3.50  
% 23.54/3.50  fof(f81,plain,(
% 23.54/3.50    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f50])).
% 23.54/3.50  
% 23.54/3.50  fof(f6,axiom,(
% 23.54/3.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 23.54/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.54/3.50  
% 23.54/3.50  fof(f27,plain,(
% 23.54/3.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.54/3.50    inference(ennf_transformation,[],[f6])).
% 23.54/3.50  
% 23.54/3.50  fof(f28,plain,(
% 23.54/3.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(flattening,[],[f27])).
% 23.54/3.50  
% 23.54/3.50  fof(f51,plain,(
% 23.54/3.50    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(nnf_transformation,[],[f28])).
% 23.54/3.50  
% 23.54/3.50  fof(f52,plain,(
% 23.54/3.50    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(rectify,[],[f51])).
% 23.54/3.50  
% 23.54/3.50  fof(f54,plain,(
% 23.54/3.50    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK2(X0))) != X1 & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f53,plain,(
% 23.54/3.50    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK1(X0),k1_lattices(X0,sK1(X0),X2)) != sK1(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 23.54/3.50    introduced(choice_axiom,[])).
% 23.54/3.50  
% 23.54/3.50  fof(f55,plain,(
% 23.54/3.50    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK1(X0),k1_lattices(X0,sK1(X0),sK2(X0))) != sK1(X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.54/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f52,f54,f53])).
% 23.54/3.50  
% 23.54/3.50  fof(f83,plain,(
% 23.54/3.50    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f55])).
% 23.54/3.50  
% 23.54/3.50  fof(f96,plain,(
% 23.54/3.50    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 23.54/3.50    inference(cnf_transformation,[],[f61])).
% 23.54/3.50  
% 23.54/3.50  cnf(c_30,plain,
% 23.54/3.50      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f101]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_37,negated_conjecture,
% 23.54/3.50      ( l3_lattices(sK8) ),
% 23.54/3.50      inference(cnf_transformation,[],[f110]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_959,plain,
% 23.54/3.50      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | sK8 != X0 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_30,c_37]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_960,plain,
% 23.54/3.50      ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8))
% 23.54/3.50      | v2_struct_0(sK8) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_959]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_40,negated_conjecture,
% 23.54/3.50      ( ~ v2_struct_0(sK8) ),
% 23.54/3.50      inference(cnf_transformation,[],[f107]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_964,plain,
% 23.54/3.50      ( m1_subset_1(k15_lattice3(sK8,X0),u1_struct_0(sK8)) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_960,c_40]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2342,plain,
% 23.54/3.50      ( m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_964]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2736,plain,
% 23.54/3.50      ( m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2342]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_22,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 23.54/3.50      | ~ l1_lattices(X1)
% 23.54/3.50      | v13_lattices(X1)
% 23.54/3.50      | v2_struct_0(X1) ),
% 23.54/3.50      inference(cnf_transformation,[],[f95]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1277,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 23.54/3.50      | ~ l1_lattices(X1)
% 23.54/3.50      | v13_lattices(X1)
% 23.54/3.50      | sK8 != X1 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_22,c_40]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1278,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | m1_subset_1(sK3(sK8,X0),u1_struct_0(sK8))
% 23.54/3.50      | ~ l1_lattices(sK8)
% 23.54/3.50      | v13_lattices(sK8) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_1277]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_18,plain,
% 23.54/3.50      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f88]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_98,plain,
% 23.54/3.50      ( l1_lattices(sK8) | ~ l3_lattices(sK8) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_18]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1282,plain,
% 23.54/3.50      ( m1_subset_1(sK3(sK8,X0),u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | v13_lattices(sK8) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_1278,c_37,c_98]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1283,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | m1_subset_1(sK3(sK8,X0),u1_struct_0(sK8))
% 23.54/3.50      | v13_lattices(sK8) ),
% 23.54/3.50      inference(renaming,[status(thm)],[c_1282]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2333,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
% 23.54/3.50      | m1_subset_1(sK3(sK8,X0_60),u1_struct_0(sK8))
% 23.54/3.50      | v13_lattices(sK8) ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_1283]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2745,plain,
% 23.54/3.50      ( m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | m1_subset_1(sK3(sK8,X0_60),u1_struct_0(sK8)) = iProver_top
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2333]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_32,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ v4_lattice3(X1)
% 23.54/3.50      | ~ l3_lattices(X1)
% 23.54/3.50      | v2_struct_0(X1)
% 23.54/3.50      | ~ v10_lattices(X1)
% 23.54/3.50      | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
% 23.54/3.50      inference(cnf_transformation,[],[f102]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_38,negated_conjecture,
% 23.54/3.50      ( v4_lattice3(sK8) ),
% 23.54/3.50      inference(cnf_transformation,[],[f109]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_739,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ l3_lattices(X1)
% 23.54/3.50      | v2_struct_0(X1)
% 23.54/3.50      | ~ v10_lattices(X1)
% 23.54/3.50      | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0
% 23.54/3.50      | sK8 != X1 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_32,c_38]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_740,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ l3_lattices(sK8)
% 23.54/3.50      | v2_struct_0(sK8)
% 23.54/3.50      | ~ v10_lattices(sK8)
% 23.54/3.50      | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X0)) = X0 ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_739]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_39,negated_conjecture,
% 23.54/3.50      ( v10_lattices(sK8) ),
% 23.54/3.50      inference(cnf_transformation,[],[f108]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_744,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X0)) = X0 ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_740,c_40,c_39,c_37]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2346,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
% 23.54/3.50      | k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X0_60)) = X0_60 ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_744]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2732,plain,
% 23.54/3.50      ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),X0_60)) = X0_60
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2346]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_3378,plain,
% 23.54/3.50      ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK3(sK8,X0_60))) = sK3(sK8,X0_60)
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2745,c_2732]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_6352,plain,
% 23.54/3.50      ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK3(sK8,k15_lattice3(sK8,X0_63)))) = sK3(sK8,k15_lattice3(sK8,X0_63))
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2736,c_3378]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_25,plain,
% 23.54/3.50      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
% 23.54/3.50      | ~ l1_lattices(X0)
% 23.54/3.50      | ~ v13_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f92]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1192,plain,
% 23.54/3.50      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
% 23.54/3.50      | ~ l1_lattices(X0)
% 23.54/3.50      | ~ v13_lattices(X0)
% 23.54/3.50      | sK8 != X0 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_25,c_40]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1193,plain,
% 23.54/3.50      ( m1_subset_1(sK4(sK8),u1_struct_0(sK8))
% 23.54/3.50      | ~ l1_lattices(sK8)
% 23.54/3.50      | ~ v13_lattices(sK8) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_1192]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1195,plain,
% 23.54/3.50      ( m1_subset_1(sK4(sK8),u1_struct_0(sK8)) | ~ v13_lattices(sK8) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_1193,c_37,c_98]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2337,plain,
% 23.54/3.50      ( m1_subset_1(sK4(sK8),u1_struct_0(sK8)) | ~ v13_lattices(sK8) ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_1195]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2741,plain,
% 23.54/3.50      ( m1_subset_1(sK4(sK8),u1_struct_0(sK8)) = iProver_top
% 23.54/3.50      | v13_lattices(sK8) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2337]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_29,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.54/3.50      | ~ l1_lattices(X1)
% 23.54/3.50      | ~ v6_lattices(X1)
% 23.54/3.50      | v2_struct_0(X1)
% 23.54/3.50      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 23.54/3.50      inference(cnf_transformation,[],[f97]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1217,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.54/3.50      | ~ l1_lattices(X1)
% 23.54/3.50      | ~ v6_lattices(X1)
% 23.54/3.50      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 23.54/3.50      | sK8 != X1 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_29,c_40]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1218,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | ~ l1_lattices(sK8)
% 23.54/3.50      | ~ v6_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_1217]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_4,plain,
% 23.54/3.50      ( v6_lattices(X0)
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | ~ v10_lattices(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f74]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_875,plain,
% 23.54/3.50      ( v6_lattices(X0)
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | sK8 != X0 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_4,c_39]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_876,plain,
% 23.54/3.50      ( v6_lattices(sK8) | ~ l3_lattices(sK8) | v2_struct_0(sK8) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_875]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_138,plain,
% 23.54/3.50      ( v6_lattices(sK8)
% 23.54/3.50      | ~ l3_lattices(sK8)
% 23.54/3.50      | v2_struct_0(sK8)
% 23.54/3.50      | ~ v10_lattices(sK8) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_4]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_878,plain,
% 23.54/3.50      ( v6_lattices(sK8) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_876,c_40,c_39,c_37,c_138]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1144,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.54/3.50      | ~ l1_lattices(X1)
% 23.54/3.50      | v2_struct_0(X1)
% 23.54/3.50      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 23.54/3.50      | sK8 != X1 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_29,c_878]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1145,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | ~ l1_lattices(sK8)
% 23.54/3.50      | v2_struct_0(sK8)
% 23.54/3.50      | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_1144]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1149,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_1145,c_40,c_37,c_98]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1221,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | k2_lattices(sK8,X1,X0) = k2_lattices(sK8,X0,X1) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_1218,c_40,c_37,c_98,c_1145]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2338,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1_60,u1_struct_0(sK8))
% 23.54/3.50      | k2_lattices(sK8,X1_60,X0_60) = k2_lattices(sK8,X0_60,X1_60) ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_1221]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2740,plain,
% 23.54/3.50      ( k2_lattices(sK8,X0_60,X1_60) = k2_lattices(sK8,X1_60,X0_60)
% 23.54/3.50      | m1_subset_1(X1_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2338]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_3350,plain,
% 23.54/3.50      ( k2_lattices(sK8,X0_60,k15_lattice3(sK8,X0_63)) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),X0_60)
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2736,c_2740]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_4538,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,X0_60)) = k2_lattices(sK8,sK3(sK8,X0_60),k15_lattice3(sK8,X0_63))
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2745,c_3350]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_9645,plain,
% 23.54/3.50      ( k2_lattices(sK8,sK3(sK8,sK3(sK8,X0_60)),k15_lattice3(sK8,X0_63)) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,X0_60)))
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2745,c_4538]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_18093,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))) = k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60))),k15_lattice3(sK8,X0_63))
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2745,c_9645]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_25948,plain,
% 23.54/3.50      ( k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))),k15_lattice3(sK8,X0_63)) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))))
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2745,c_18093]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_40328,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))))) = k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60))))),k15_lattice3(sK8,X0_63))
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2745,c_25948]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2356,plain,
% 23.54/3.50      ( X0_63 != X1_63
% 23.54/3.50      | k15_lattice3(X0_62,X0_63) = k15_lattice3(X0_62,X1_63) ),
% 23.54/3.50      theory(equality) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2361,plain,
% 23.54/3.50      ( k1_xboole_0 != k1_xboole_0
% 23.54/3.50      | k15_lattice3(sK8,k1_xboole_0) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2356]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2351,plain,( X0_63 = X0_63 ),theory(equality) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2365,plain,
% 23.54/3.50      ( k1_xboole_0 = k1_xboole_0 ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2351]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_36,negated_conjecture,
% 23.54/3.50      ( ~ v13_lattices(sK8)
% 23.54/3.50      | ~ l3_lattices(sK8)
% 23.54/3.50      | v2_struct_0(sK8)
% 23.54/3.50      | ~ v10_lattices(sK8)
% 23.54/3.50      | k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f111]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_239,negated_conjecture,
% 23.54/3.50      ( ~ v13_lattices(sK8)
% 23.54/3.50      | k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_36,c_40,c_39,c_37]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2348,negated_conjecture,
% 23.54/3.50      ( ~ v13_lattices(sK8)
% 23.54/3.50      | k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_239]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2366,plain,
% 23.54/3.50      ( k5_lattices(sK8) != k15_lattice3(sK8,k1_xboole_0)
% 23.54/3.50      | v13_lattices(sK8) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2348]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2382,plain,
% 23.54/3.50      ( m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2342]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2384,plain,
% 23.54/3.50      ( m1_subset_1(k15_lattice3(sK8,k1_xboole_0),u1_struct_0(sK8)) = iProver_top ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2382]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_8,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 23.54/3.50      | ~ l1_lattices(X1)
% 23.54/3.50      | ~ v13_lattices(X1)
% 23.54/3.50      | v2_struct_0(X1)
% 23.54/3.50      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
% 23.54/3.50      inference(cnf_transformation,[],[f112]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1343,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 23.54/3.50      | ~ l1_lattices(X1)
% 23.54/3.50      | ~ v13_lattices(X1)
% 23.54/3.50      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1)
% 23.54/3.50      | sK8 != X1 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_8,c_40]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1344,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8))
% 23.54/3.50      | ~ l1_lattices(sK8)
% 23.54/3.50      | ~ v13_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,X0,k5_lattices(sK8)) = k5_lattices(sK8) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_1343]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_16,plain,
% 23.54/3.50      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 23.54/3.50      | ~ l1_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f87]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_104,plain,
% 23.54/3.50      ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8))
% 23.54/3.50      | ~ l1_lattices(sK8)
% 23.54/3.50      | v2_struct_0(sK8) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_16]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1348,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ v13_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,X0,k5_lattices(sK8)) = k5_lattices(sK8) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_1344,c_40,c_37,c_98,c_104]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2330,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
% 23.54/3.50      | ~ v13_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,X0_60,k5_lattices(sK8)) = k5_lattices(sK8) ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_1348]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2939,plain,
% 23.54/3.50      ( ~ m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8))
% 23.54/3.50      | ~ v13_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) = k5_lattices(sK8) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2330]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2940,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) = k5_lattices(sK8)
% 23.54/3.50      | m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2939]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2942,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) = k5_lattices(sK8)
% 23.54/3.50      | m1_subset_1(k15_lattice3(sK8,k1_xboole_0),u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) != iProver_top ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2940]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2350,plain,( X0_60 = X0_60 ),theory(equality) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_3185,plain,
% 23.54/3.50      ( k5_lattices(sK8) = k5_lattices(sK8) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2350]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2352,plain,
% 23.54/3.50      ( X0_60 != X1_60 | X2_60 != X1_60 | X2_60 = X0_60 ),
% 23.54/3.50      theory(equality) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2905,plain,
% 23.54/3.50      ( X0_60 != X1_60
% 23.54/3.50      | k5_lattices(sK8) != X1_60
% 23.54/3.50      | k5_lattices(sK8) = X0_60 ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2352]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_3187,plain,
% 23.54/3.50      ( X0_60 != k5_lattices(sK8)
% 23.54/3.50      | k5_lattices(sK8) = X0_60
% 23.54/3.50      | k5_lattices(sK8) != k5_lattices(sK8) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2905]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_3801,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) != k5_lattices(sK8)
% 23.54/3.50      | k5_lattices(sK8) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))
% 23.54/3.50      | k5_lattices(sK8) != k5_lattices(sK8) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_3187]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_3807,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) != k5_lattices(sK8)
% 23.54/3.50      | k5_lattices(sK8) = k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8))
% 23.54/3.50      | k5_lattices(sK8) != k5_lattices(sK8) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_3801]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2895,plain,
% 23.54/3.50      ( k15_lattice3(sK8,k1_xboole_0) != X0_60
% 23.54/3.50      | k5_lattices(sK8) != X0_60
% 23.54/3.50      | k5_lattices(sK8) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2352]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_5333,plain,
% 23.54/3.50      ( k15_lattice3(sK8,k1_xboole_0) != k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))
% 23.54/3.50      | k5_lattices(sK8) != k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))
% 23.54/3.50      | k5_lattices(sK8) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2895]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_5334,plain,
% 23.54/3.50      ( k15_lattice3(sK8,k1_xboole_0) != k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8))
% 23.54/3.50      | k5_lattices(sK8) != k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8))
% 23.54/3.50      | k5_lattices(sK8) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_5333]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_7784,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) != X0_60
% 23.54/3.50      | k15_lattice3(sK8,k1_xboole_0) != X0_60
% 23.54/3.50      | k15_lattice3(sK8,k1_xboole_0) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2352]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_28233,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8)) != k15_lattice3(sK8,k1_xboole_0)
% 23.54/3.50      | k15_lattice3(sK8,k1_xboole_0) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))
% 23.54/3.50      | k15_lattice3(sK8,k1_xboole_0) != k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_7784]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_28234,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) != k15_lattice3(sK8,k1_xboole_0)
% 23.54/3.50      | k15_lattice3(sK8,k1_xboole_0) = k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8))
% 23.54/3.50      | k15_lattice3(sK8,k1_xboole_0) != k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_28233]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1206,plain,
% 23.54/3.50      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 23.54/3.50      | ~ l1_lattices(X0)
% 23.54/3.50      | sK8 != X0 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_16,c_40]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1207,plain,
% 23.54/3.50      ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8))
% 23.54/3.50      | ~ l1_lattices(sK8) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_1206]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1209,plain,
% 23.54/3.50      ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8)) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_1207,c_40,c_37,c_98,c_104]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2336,plain,
% 23.54/3.50      ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8)) ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_1209]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2742,plain,
% 23.54/3.50      ( m1_subset_1(k5_lattices(sK8),u1_struct_0(sK8)) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2336]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2947,plain,
% 23.54/3.50      ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),k5_lattices(sK8))) = k5_lattices(sK8) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2742,c_2732]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_0,plain,
% 23.54/3.50      ( r1_tarski(k1_xboole_0,X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f71]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1,plain,
% 23.54/3.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f72]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_460,plain,
% 23.54/3.50      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_461,plain,
% 23.54/3.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_460]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_34,plain,
% 23.54/3.50      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 23.54/3.50      | r2_hidden(sK7(X0,X1,X2),X1)
% 23.54/3.50      | ~ v4_lattice3(X0)
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | ~ v10_lattices(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f105]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_697,plain,
% 23.54/3.50      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 23.54/3.50      | r2_hidden(sK7(X0,X1,X2),X1)
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | ~ v10_lattices(X0)
% 23.54/3.50      | sK8 != X0 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_34,c_38]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_698,plain,
% 23.54/3.50      ( r3_lattices(sK8,k15_lattice3(sK8,X0),k15_lattice3(sK8,X1))
% 23.54/3.50      | r2_hidden(sK7(sK8,X0,X1),X0)
% 23.54/3.50      | ~ l3_lattices(sK8)
% 23.54/3.50      | v2_struct_0(sK8)
% 23.54/3.50      | ~ v10_lattices(sK8) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_697]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_702,plain,
% 23.54/3.50      ( r2_hidden(sK7(sK8,X0,X1),X0)
% 23.54/3.50      | r3_lattices(sK8,k15_lattice3(sK8,X0),k15_lattice3(sK8,X1)) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_698,c_40,c_39,c_37]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_703,plain,
% 23.54/3.50      ( r3_lattices(sK8,k15_lattice3(sK8,X0),k15_lattice3(sK8,X1))
% 23.54/3.50      | r2_hidden(sK7(sK8,X0,X1),X0) ),
% 23.54/3.50      inference(renaming,[status(thm)],[c_702]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_812,plain,
% 23.54/3.50      ( r3_lattices(sK8,k15_lattice3(sK8,X0),k15_lattice3(sK8,X1))
% 23.54/3.50      | sK7(sK8,X0,X1) != X2
% 23.54/3.50      | k1_xboole_0 != X0 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_461,c_703]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_813,plain,
% 23.54/3.50      ( r3_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0)) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_812]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2343,plain,
% 23.54/3.50      ( r3_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_813]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2735,plain,
% 23.54/3.50      ( r3_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2343]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_3,plain,
% 23.54/3.50      ( v8_lattices(X0)
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | ~ v10_lattices(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f75]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_20,plain,
% 23.54/3.50      ( ~ r3_lattices(X0,X1,X2)
% 23.54/3.50      | r1_lattices(X0,X1,X2)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.54/3.50      | ~ v6_lattices(X0)
% 23.54/3.50      | ~ v8_lattices(X0)
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | ~ v9_lattices(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f90]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_599,plain,
% 23.54/3.50      ( ~ r3_lattices(X0,X1,X2)
% 23.54/3.50      | r1_lattices(X0,X1,X2)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.54/3.50      | ~ v6_lattices(X0)
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | ~ v10_lattices(X0)
% 23.54/3.50      | ~ v9_lattices(X0) ),
% 23.54/3.50      inference(resolution,[status(thm)],[c_3,c_20]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2,plain,
% 23.54/3.50      ( ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | ~ v10_lattices(X0)
% 23.54/3.50      | v9_lattices(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f76]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_603,plain,
% 23.54/3.50      ( ~ v10_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | ~ r3_lattices(X0,X1,X2)
% 23.54/3.50      | r1_lattices(X0,X1,X2)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_599,c_20,c_4,c_3,c_2]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_604,plain,
% 23.54/3.50      ( ~ r3_lattices(X0,X1,X2)
% 23.54/3.50      | r1_lattices(X0,X1,X2)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | ~ v10_lattices(X0) ),
% 23.54/3.50      inference(renaming,[status(thm)],[c_603]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_851,plain,
% 23.54/3.50      ( ~ r3_lattices(X0,X1,X2)
% 23.54/3.50      | r1_lattices(X0,X1,X2)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | sK8 != X0 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_604,c_39]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_852,plain,
% 23.54/3.50      ( ~ r3_lattices(sK8,X0,X1)
% 23.54/3.50      | r1_lattices(sK8,X0,X1)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ l3_lattices(sK8)
% 23.54/3.50      | v2_struct_0(sK8) ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_851]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_856,plain,
% 23.54/3.50      ( ~ r3_lattices(sK8,X0,X1)
% 23.54/3.50      | r1_lattices(sK8,X0,X1)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_852,c_40,c_37]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_857,plain,
% 23.54/3.50      ( ~ r3_lattices(sK8,X0,X1)
% 23.54/3.50      | r1_lattices(sK8,X0,X1)
% 23.54/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
% 23.54/3.50      inference(renaming,[status(thm)],[c_856]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_17,plain,
% 23.54/3.50      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 23.54/3.50      inference(cnf_transformation,[],[f89]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_11,plain,
% 23.54/3.50      ( ~ r1_lattices(X0,X1,X2)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.54/3.50      | ~ l2_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | k1_lattices(X0,X1,X2) = X2 ),
% 23.54/3.50      inference(cnf_transformation,[],[f81]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_471,plain,
% 23.54/3.50      ( ~ r1_lattices(X0,X1,X2)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.54/3.50      | ~ l3_lattices(X0)
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | k1_lattices(X0,X1,X2) = X2 ),
% 23.54/3.50      inference(resolution,[status(thm)],[c_17,c_11]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_935,plain,
% 23.54/3.50      ( ~ r1_lattices(X0,X1,X2)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.54/3.50      | v2_struct_0(X0)
% 23.54/3.50      | k1_lattices(X0,X1,X2) = X2
% 23.54/3.50      | sK8 != X0 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_471,c_37]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_936,plain,
% 23.54/3.50      ( ~ r1_lattices(sK8,X0,X1)
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | v2_struct_0(sK8)
% 23.54/3.50      | k1_lattices(sK8,X0,X1) = X1 ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_935]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_940,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | ~ r1_lattices(sK8,X0,X1)
% 23.54/3.50      | k1_lattices(sK8,X0,X1) = X1 ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_936,c_40]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_941,plain,
% 23.54/3.50      ( ~ r1_lattices(sK8,X0,X1)
% 23.54/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | k1_lattices(sK8,X0,X1) = X1 ),
% 23.54/3.50      inference(renaming,[status(thm)],[c_940]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1044,plain,
% 23.54/3.50      ( ~ r3_lattices(sK8,X0,X1)
% 23.54/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | k1_lattices(sK8,X0,X1) = X1 ),
% 23.54/3.50      inference(resolution,[status(thm)],[c_857,c_941]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2339,plain,
% 23.54/3.50      ( ~ r3_lattices(sK8,X0_60,X1_60)
% 23.54/3.50      | ~ m1_subset_1(X0_60,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1_60,u1_struct_0(sK8))
% 23.54/3.50      | k1_lattices(sK8,X0_60,X1_60) = X1_60 ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_1044]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2739,plain,
% 23.54/3.50      ( k1_lattices(sK8,X0_60,X1_60) = X1_60
% 23.54/3.50      | r3_lattices(sK8,X0_60,X1_60) != iProver_top
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | m1_subset_1(X1_60,u1_struct_0(sK8)) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2339]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_4939,plain,
% 23.54/3.50      ( k1_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) = k15_lattice3(sK8,X0_63)
% 23.54/3.50      | m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | m1_subset_1(k15_lattice3(sK8,k1_xboole_0),u1_struct_0(sK8)) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2735,c_2739]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_16250,plain,
% 23.54/3.50      ( k1_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) = k15_lattice3(sK8,X0_63) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_4939,c_2382,c_2384]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_16253,plain,
% 23.54/3.50      ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),k5_lattices(sK8))) = k1_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2947,c_16250]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_16258,plain,
% 23.54/3.50      ( k1_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) = k5_lattices(sK8) ),
% 23.54/3.50      inference(light_normalisation,[status(thm)],[c_16253,c_2947]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_15,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.54/3.50      | ~ l3_lattices(X1)
% 23.54/3.50      | v2_struct_0(X1)
% 23.54/3.50      | ~ v9_lattices(X1)
% 23.54/3.50      | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0 ),
% 23.54/3.50      inference(cnf_transformation,[],[f83]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_987,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.54/3.50      | v2_struct_0(X1)
% 23.54/3.50      | ~ v9_lattices(X1)
% 23.54/3.50      | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0
% 23.54/3.50      | sK8 != X1 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_15,c_37]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_988,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | v2_struct_0(sK8)
% 23.54/3.50      | ~ v9_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_987]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_144,plain,
% 23.54/3.50      ( ~ l3_lattices(sK8)
% 23.54/3.50      | v2_struct_0(sK8)
% 23.54/3.50      | ~ v10_lattices(sK8)
% 23.54/3.50      | v9_lattices(sK8) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_992,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 23.54/3.50      | k2_lattices(sK8,X1,k1_lattices(sK8,X1,X0)) = X1 ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_988,c_40,c_39,c_37,c_144]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2341,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
% 23.54/3.50      | ~ m1_subset_1(X1_60,u1_struct_0(sK8))
% 23.54/3.50      | k2_lattices(sK8,X1_60,k1_lattices(sK8,X1_60,X0_60)) = X1_60 ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_992]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2737,plain,
% 23.54/3.50      ( k2_lattices(sK8,X0_60,k1_lattices(sK8,X0_60,X1_60)) = X0_60
% 23.54/3.50      | m1_subset_1(X1_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2341]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_3260,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k1_lattices(sK8,k15_lattice3(sK8,X0_63),X0_60)) = k15_lattice3(sK8,X0_63)
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2736,c_2737]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_4923,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k1_lattices(sK8,k15_lattice3(sK8,X0_63),k5_lattices(sK8))) = k15_lattice3(sK8,X0_63) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2742,c_3260]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_59067,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k5_lattices(sK8)) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_16258,c_4923]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_59081,plain,
% 23.54/3.50      ( m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))))) = k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60))))),k15_lattice3(sK8,X0_63)) ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_40328,c_2361,c_2365,c_2366,c_2384,c_2942,c_3185,
% 23.54/3.50                 c_3807,c_5334,c_28234,c_59067]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_59082,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60)))))) = k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,X0_60))))),k15_lattice3(sK8,X0_63))
% 23.54/3.50      | m1_subset_1(X0_60,u1_struct_0(sK8)) != iProver_top ),
% 23.54/3.50      inference(renaming,[status(thm)],[c_59081]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_59087,plain,
% 23.54/3.50      ( k2_lattices(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK4(sK8)))))),k15_lattice3(sK8,X0_63)) = k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK3(sK8,sK4(sK8)))))))
% 23.54/3.50      | v13_lattices(sK8) != iProver_top ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2741,c_59082]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_59369,plain,
% 23.54/3.50      ( v13_lattices(sK8) != iProver_top ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_59087,c_2361,c_2365,c_2366,c_2384,c_2942,c_3185,
% 23.54/3.50                 c_3807,c_5334,c_28234,c_59067]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_59507,plain,
% 23.54/3.50      ( k15_lattice3(sK8,k6_domain_1(u1_struct_0(sK8),sK3(sK8,k15_lattice3(sK8,X0_63)))) = sK3(sK8,k15_lattice3(sK8,X0_63)) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_6352,c_59369]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_4926,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k1_lattices(sK8,k15_lattice3(sK8,X0_63),k15_lattice3(sK8,X1_63))) = k15_lattice3(sK8,X0_63) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2736,c_3260]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_16256,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),k15_lattice3(sK8,X0_63)) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_16250,c_4926]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_65220,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),sK3(sK8,k15_lattice3(sK8,X0_63))) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_59507,c_16256]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_65368,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),sK3(sK8,k15_lattice3(sK8,k1_xboole_0))) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_65220]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_4539,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k15_lattice3(sK8,X1_63)) = k2_lattices(sK8,k15_lattice3(sK8,X1_63),k15_lattice3(sK8,X0_63)) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_2736,c_3350]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_61432,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),k15_lattice3(sK8,k1_xboole_0)) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_16256,c_4539]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_65208,plain,
% 23.54/3.50      ( k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,X0_63)),k15_lattice3(sK8,k1_xboole_0)) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(superposition,[status(thm)],[c_59507,c_61432]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_65367,plain,
% 23.54/3.50      ( k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,k1_xboole_0)),k15_lattice3(sK8,k1_xboole_0)) = k15_lattice3(sK8,k1_xboole_0) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_65208]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_21,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ l1_lattices(X1)
% 23.54/3.50      | v13_lattices(X1)
% 23.54/3.50      | v2_struct_0(X1)
% 23.54/3.50      | k2_lattices(X1,X0,sK3(X1,X0)) != X0
% 23.54/3.50      | k2_lattices(X1,sK3(X1,X0),X0) != X0 ),
% 23.54/3.50      inference(cnf_transformation,[],[f96]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1298,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.54/3.50      | ~ l1_lattices(X1)
% 23.54/3.50      | v13_lattices(X1)
% 23.54/3.50      | k2_lattices(X1,X0,sK3(X1,X0)) != X0
% 23.54/3.50      | k2_lattices(X1,sK3(X1,X0),X0) != X0
% 23.54/3.50      | sK8 != X1 ),
% 23.54/3.50      inference(resolution_lifted,[status(thm)],[c_21,c_40]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1299,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | ~ l1_lattices(sK8)
% 23.54/3.50      | v13_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,X0,sK3(sK8,X0)) != X0
% 23.54/3.50      | k2_lattices(sK8,sK3(sK8,X0),X0) != X0 ),
% 23.54/3.50      inference(unflattening,[status(thm)],[c_1298]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_1303,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 23.54/3.50      | v13_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,X0,sK3(sK8,X0)) != X0
% 23.54/3.50      | k2_lattices(sK8,sK3(sK8,X0),X0) != X0 ),
% 23.54/3.50      inference(global_propositional_subsumption,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_1299,c_37,c_98]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2332,plain,
% 23.54/3.50      ( ~ m1_subset_1(X0_60,u1_struct_0(sK8))
% 23.54/3.50      | v13_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,X0_60,sK3(sK8,X0_60)) != X0_60
% 23.54/3.50      | k2_lattices(sK8,sK3(sK8,X0_60),X0_60) != X0_60 ),
% 23.54/3.50      inference(subtyping,[status(esa)],[c_1303]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2838,plain,
% 23.54/3.50      ( ~ m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8))
% 23.54/3.50      | v13_lattices(sK8)
% 23.54/3.50      | k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,k15_lattice3(sK8,X0_63))) != k15_lattice3(sK8,X0_63)
% 23.54/3.50      | k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,X0_63)),k15_lattice3(sK8,X0_63)) != k15_lattice3(sK8,X0_63) ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2332]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2839,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,X0_63),sK3(sK8,k15_lattice3(sK8,X0_63))) != k15_lattice3(sK8,X0_63)
% 23.54/3.50      | k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,X0_63)),k15_lattice3(sK8,X0_63)) != k15_lattice3(sK8,X0_63)
% 23.54/3.50      | m1_subset_1(k15_lattice3(sK8,X0_63),u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(predicate_to_equality,[status(thm)],[c_2838]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(c_2841,plain,
% 23.54/3.50      ( k2_lattices(sK8,k15_lattice3(sK8,k1_xboole_0),sK3(sK8,k15_lattice3(sK8,k1_xboole_0))) != k15_lattice3(sK8,k1_xboole_0)
% 23.54/3.50      | k2_lattices(sK8,sK3(sK8,k15_lattice3(sK8,k1_xboole_0)),k15_lattice3(sK8,k1_xboole_0)) != k15_lattice3(sK8,k1_xboole_0)
% 23.54/3.50      | m1_subset_1(k15_lattice3(sK8,k1_xboole_0),u1_struct_0(sK8)) != iProver_top
% 23.54/3.50      | v13_lattices(sK8) = iProver_top ),
% 23.54/3.50      inference(instantiation,[status(thm)],[c_2839]) ).
% 23.54/3.50  
% 23.54/3.50  cnf(contradiction,plain,
% 23.54/3.50      ( $false ),
% 23.54/3.50      inference(minisat,
% 23.54/3.50                [status(thm)],
% 23.54/3.50                [c_65368,c_65367,c_59369,c_2841,c_2384]) ).
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.54/3.50  
% 23.54/3.50  ------                               Statistics
% 23.54/3.50  
% 23.54/3.50  ------ General
% 23.54/3.50  
% 23.54/3.50  abstr_ref_over_cycles:                  0
% 23.54/3.50  abstr_ref_under_cycles:                 0
% 23.54/3.50  gc_basic_clause_elim:                   0
% 23.54/3.50  forced_gc_time:                         0
% 23.54/3.50  parsing_time:                           0.01
% 23.54/3.50  unif_index_cands_time:                  0.
% 23.54/3.50  unif_index_add_time:                    0.
% 23.54/3.50  orderings_time:                         0.
% 23.54/3.50  out_proof_time:                         0.026
% 23.54/3.50  total_time:                             2.746
% 23.54/3.50  num_of_symbols:                         64
% 23.54/3.50  num_of_terms:                           62274
% 23.54/3.50  
% 23.54/3.50  ------ Preprocessing
% 23.54/3.50  
% 23.54/3.50  num_of_splits:                          0
% 23.54/3.50  num_of_split_atoms:                     0
% 23.54/3.50  num_of_reused_defs:                     0
% 23.54/3.50  num_eq_ax_congr_red:                    56
% 23.54/3.50  num_of_sem_filtered_clauses:            1
% 23.54/3.50  num_of_subtypes:                        4
% 23.54/3.50  monotx_restored_types:                  0
% 23.54/3.50  sat_num_of_epr_types:                   0
% 23.54/3.50  sat_num_of_non_cyclic_types:            0
% 23.54/3.50  sat_guarded_non_collapsed_types:        1
% 23.54/3.50  num_pure_diseq_elim:                    0
% 23.54/3.50  simp_replaced_by:                       0
% 23.54/3.50  res_preprocessed:                       120
% 23.54/3.50  prep_upred:                             0
% 23.54/3.50  prep_unflattend:                        45
% 23.54/3.50  smt_new_axioms:                         0
% 23.54/3.50  pred_elim_cands:                        3
% 23.54/3.50  pred_elim:                              12
% 23.54/3.50  pred_elim_cl:                           19
% 23.54/3.50  pred_elim_cycles:                       16
% 23.54/3.50  merged_defs:                            0
% 23.54/3.50  merged_defs_ncl:                        0
% 23.54/3.50  bin_hyper_res:                          0
% 23.54/3.50  prep_cycles:                            4
% 23.54/3.50  pred_elim_time:                         0.031
% 23.54/3.50  splitting_time:                         0.
% 23.54/3.50  sem_filter_time:                        0.
% 23.54/3.50  monotx_time:                            0.
% 23.54/3.50  subtype_inf_time:                       0.
% 23.54/3.50  
% 23.54/3.50  ------ Problem properties
% 23.54/3.50  
% 23.54/3.50  clauses:                                21
% 23.54/3.50  conjectures:                            1
% 23.54/3.50  epr:                                    0
% 23.54/3.50  horn:                                   17
% 23.54/3.50  ground:                                 3
% 23.54/3.50  unary:                                  3
% 23.54/3.50  binary:                                 5
% 23.54/3.50  lits:                                   58
% 23.54/3.50  lits_eq:                                17
% 23.54/3.50  fd_pure:                                0
% 23.54/3.50  fd_pseudo:                              0
% 23.54/3.50  fd_cond:                                2
% 23.54/3.50  fd_pseudo_cond:                         0
% 23.54/3.50  ac_symbols:                             0
% 23.54/3.50  
% 23.54/3.50  ------ Propositional Solver
% 23.54/3.50  
% 23.54/3.50  prop_solver_calls:                      44
% 23.54/3.50  prop_fast_solver_calls:                 2705
% 23.54/3.50  smt_solver_calls:                       0
% 23.54/3.50  smt_fast_solver_calls:                  0
% 23.54/3.50  prop_num_of_clauses:                    43272
% 23.54/3.50  prop_preprocess_simplified:             35927
% 23.54/3.50  prop_fo_subsumed:                       85
% 23.54/3.50  prop_solver_time:                       0.
% 23.54/3.50  smt_solver_time:                        0.
% 23.54/3.50  smt_fast_solver_time:                   0.
% 23.54/3.50  prop_fast_solver_time:                  0.
% 23.54/3.50  prop_unsat_core_time:                   0.003
% 23.54/3.50  
% 23.54/3.50  ------ QBF
% 23.54/3.50  
% 23.54/3.50  qbf_q_res:                              0
% 23.54/3.50  qbf_num_tautologies:                    0
% 23.54/3.50  qbf_prep_cycles:                        0
% 23.54/3.50  
% 23.54/3.50  ------ BMC1
% 23.54/3.50  
% 23.54/3.50  bmc1_current_bound:                     -1
% 23.54/3.50  bmc1_last_solved_bound:                 -1
% 23.54/3.50  bmc1_unsat_core_size:                   -1
% 23.54/3.50  bmc1_unsat_core_parents_size:           -1
% 23.54/3.50  bmc1_merge_next_fun:                    0
% 23.54/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.54/3.50  
% 23.54/3.50  ------ Instantiation
% 23.54/3.50  
% 23.54/3.50  inst_num_of_clauses:                    6081
% 23.54/3.50  inst_num_in_passive:                    1154
% 23.54/3.50  inst_num_in_active:                     1913
% 23.54/3.50  inst_num_in_unprocessed:                3014
% 23.54/3.50  inst_num_of_loops:                      2720
% 23.54/3.50  inst_num_of_learning_restarts:          0
% 23.54/3.50  inst_num_moves_active_passive:          805
% 23.54/3.50  inst_lit_activity:                      0
% 23.54/3.50  inst_lit_activity_moves:                3
% 23.54/3.50  inst_num_tautologies:                   0
% 23.54/3.50  inst_num_prop_implied:                  0
% 23.54/3.50  inst_num_existing_simplified:           0
% 23.54/3.50  inst_num_eq_res_simplified:             0
% 23.54/3.50  inst_num_child_elim:                    0
% 23.54/3.50  inst_num_of_dismatching_blockings:      5236
% 23.54/3.50  inst_num_of_non_proper_insts:           6305
% 23.54/3.50  inst_num_of_duplicates:                 0
% 23.54/3.50  inst_inst_num_from_inst_to_res:         0
% 23.54/3.50  inst_dismatching_checking_time:         0.
% 23.54/3.50  
% 23.54/3.50  ------ Resolution
% 23.54/3.50  
% 23.54/3.50  res_num_of_clauses:                     0
% 23.54/3.50  res_num_in_passive:                     0
% 23.54/3.50  res_num_in_active:                      0
% 23.54/3.50  res_num_of_loops:                       124
% 23.54/3.50  res_forward_subset_subsumed:            262
% 23.54/3.50  res_backward_subset_subsumed:           0
% 23.54/3.50  res_forward_subsumed:                   0
% 23.54/3.50  res_backward_subsumed:                  0
% 23.54/3.50  res_forward_subsumption_resolution:     1
% 23.54/3.50  res_backward_subsumption_resolution:    0
% 23.54/3.50  res_clause_to_clause_subsumption:       31513
% 23.54/3.50  res_orphan_elimination:                 0
% 23.54/3.50  res_tautology_del:                      184
% 23.54/3.50  res_num_eq_res_simplified:              0
% 23.54/3.50  res_num_sel_changes:                    0
% 23.54/3.50  res_moves_from_active_to_pass:          0
% 23.54/3.50  
% 23.54/3.50  ------ Superposition
% 23.54/3.50  
% 23.54/3.50  sup_time_total:                         0.
% 23.54/3.50  sup_time_generating:                    0.
% 23.54/3.50  sup_time_sim_full:                      0.
% 23.54/3.50  sup_time_sim_immed:                     0.
% 23.54/3.50  
% 23.54/3.50  sup_num_of_clauses:                     6035
% 23.54/3.50  sup_num_in_active:                      248
% 23.54/3.50  sup_num_in_passive:                     5787
% 23.54/3.50  sup_num_of_loops:                       543
% 23.54/3.50  sup_fw_superposition:                   5523
% 23.54/3.50  sup_bw_superposition:                   8560
% 23.54/3.50  sup_immediate_simplified:               214
% 23.54/3.50  sup_given_eliminated:                   0
% 23.54/3.50  comparisons_done:                       0
% 23.54/3.50  comparisons_avoided:                    369
% 23.54/3.50  
% 23.54/3.50  ------ Simplifications
% 23.54/3.50  
% 23.54/3.50  
% 23.54/3.50  sim_fw_subset_subsumed:                 16
% 23.54/3.50  sim_bw_subset_subsumed:                 7013
% 23.54/3.50  sim_fw_subsumed:                        9
% 23.54/3.50  sim_bw_subsumed:                        157
% 23.54/3.50  sim_fw_subsumption_res:                 0
% 23.54/3.50  sim_bw_subsumption_res:                 0
% 23.54/3.50  sim_tautology_del:                      190
% 23.54/3.50  sim_eq_tautology_del:                   68
% 23.54/3.50  sim_eq_res_simp:                        0
% 23.54/3.50  sim_fw_demodulated:                     124
% 23.54/3.50  sim_bw_demodulated:                     1
% 23.54/3.50  sim_light_normalised:                   97
% 23.54/3.50  sim_joinable_taut:                      0
% 23.54/3.50  sim_joinable_simp:                      0
% 23.54/3.50  sim_ac_normalised:                      0
% 23.54/3.50  sim_smt_subsumption:                    0
% 23.54/3.50  
%------------------------------------------------------------------------------
