%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:21 EST 2020

% Result     : Theorem 7.99s
% Output     : CNFRefutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :  242 (5189 expanded)
%              Number of clauses        :  156 (1474 expanded)
%              Number of leaves         :   25 (1024 expanded)
%              Depth                    :   28
%              Number of atoms          : 1052 (34247 expanded)
%              Number of equality atoms :  292 (4249 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f62,plain,
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
   => ( ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
        | ~ l3_lattices(sK6)
        | ~ v13_lattices(sK6)
        | ~ v10_lattices(sK6)
        | v2_struct_0(sK6) )
      & l3_lattices(sK6)
      & v4_lattice3(sK6)
      & v10_lattices(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
      | ~ l3_lattices(sK6)
      | ~ v13_lattices(sK6)
      | ~ v10_lattices(sK6)
      | v2_struct_0(sK6) )
    & l3_lattices(sK6)
    & v4_lattice3(sK6)
    & v10_lattices(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f62])).

fof(f98,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f95,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f9,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f32])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f53,plain,(
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

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f51,f53,f52])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f96,plain,(
    v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f55,plain,(
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

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK4(X0)) != k2_lattices(X0,sK4(X0),X1)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,X2,sK3(X0)) != k2_lattices(X0,sK3(X0),X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK3(X0),sK4(X0)) != k2_lattices(X0,sK4(X0),sK3(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).

fof(f85,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

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

fof(f67,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,
    ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
    | ~ l3_lattices(sK6)
    | ~ v13_lattices(sK6)
    | ~ v10_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f30])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f60,plain,(
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
            | ~ r3_lattices(X0,sK5(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X0,sK5(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(sK5(X0,X1,X2),X1)
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f60])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_32,negated_conjecture,
    ( l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_785,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_786,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_790,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_786,c_35])).

cnf(c_2119,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_790])).

cnf(c_2497,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2119])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_1063,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | v13_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_1062])).

cnf(c_11,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_99,plain,
    ( l1_lattices(sK6)
    | ~ l3_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1067,plain,
    ( m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v13_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1063,c_32,c_99])).

cnf(c_1068,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
    | v13_lattices(sK6) ),
    inference(renaming,[status(thm)],[c_1067])).

cnf(c_2111,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | m1_subset_1(sK1(sK6,X0_56),u1_struct_0(sK6))
    | v13_lattices(sK6) ),
    inference(subtyping,[status(esa)],[c_1068])).

cnf(c_2505,plain,
    ( m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(sK6,X0_56),u1_struct_0(sK6)) = iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2111])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_33,negated_conjecture,
    ( v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6)
    | k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_34,negated_conjecture,
    ( v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_35,c_34,c_32])).

cnf(c_2123,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X0_56)) = X0_56 ),
    inference(subtyping,[status(esa)],[c_547])).

cnf(c_2493,plain,
    ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X0_56)) = X0_56
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2123])).

cnf(c_3192,plain,
    ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK1(sK6,X0_56))) = sK1(sK6,X0_56)
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2505,c_2493])).

cnf(c_4639,plain,
    ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK1(sK6,k15_lattice3(sK6,X0_59)))) = sK1(sK6,k15_lattice3(sK6,X0_59))
    | v13_lattices(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_3192])).

cnf(c_20,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | ~ v13_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_977,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | ~ v13_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_978,plain,
    ( m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | ~ v13_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_977])).

cnf(c_980,plain,
    ( m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | ~ v13_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_978,c_32,c_99])).

cnf(c_2115,plain,
    ( m1_subset_1(sK2(sK6),u1_struct_0(sK6))
    | ~ v13_lattices(sK6) ),
    inference(subtyping,[status(esa)],[c_980])).

cnf(c_2501,plain,
    ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) = iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2115])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1002,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_1003,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | ~ v6_lattices(sK6)
    | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1002])).

cnf(c_4,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_630,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_34])).

cnf(c_631,plain,
    ( v6_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_630])).

cnf(c_118,plain,
    ( v6_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_633,plain,
    ( v6_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_631,c_35,c_34,c_32,c_118])).

cnf(c_929,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_633])).

cnf(c_930,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | v2_struct_0(sK6)
    | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_934,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_35,c_32,c_99])).

cnf(c_1006,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1003,c_35,c_32,c_99,c_930])).

cnf(c_2116,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | k2_lattices(sK6,X1_56,X0_56) = k2_lattices(sK6,X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_1006])).

cnf(c_2500,plain,
    ( k2_lattices(sK6,X0_56,X1_56) = k2_lattices(sK6,X1_56,X0_56)
    | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2116])).

cnf(c_3186,plain,
    ( k2_lattices(sK6,X0_56,sK1(sK6,X1_56)) = k2_lattices(sK6,sK1(sK6,X1_56),X0_56)
    | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2505,c_2500])).

cnf(c_5835,plain,
    ( k2_lattices(sK6,sK1(sK6,X0_56),sK1(sK6,X1_56)) = k2_lattices(sK6,sK1(sK6,X1_56),sK1(sK6,X0_56))
    | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2505,c_3186])).

cnf(c_12362,plain,
    ( k2_lattices(sK6,sK1(sK6,X0_56),sK1(sK6,k15_lattice3(sK6,X0_59))) = k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),sK1(sK6,X0_56))
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_5835])).

cnf(c_36,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_39,plain,
    ( l3_lattices(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_98,plain,
    ( l1_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_100,plain,
    ( l1_lattices(sK6) = iProver_top
    | l3_lattices(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_10,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_101,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) = iProver_top
    | l1_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_103,plain,
    ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) = iProver_top
    | l1_lattices(sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_2133,plain,
    ( X0_59 != X1_59
    | k15_lattice3(X0_58,X0_59) = k15_lattice3(X0_58,X1_59) ),
    theory(equality)).

cnf(c_2138,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k15_lattice3(sK6,k1_xboole_0) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_2128,plain,
    ( X0_59 = X0_59 ),
    theory(equality)).

cnf(c_2142,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_31,negated_conjecture,
    ( ~ v13_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6)
    | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_209,negated_conjecture,
    ( ~ v13_lattices(sK6)
    | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_35,c_34,c_32])).

cnf(c_2125,negated_conjecture,
    ( ~ v13_lattices(sK6)
    | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_209])).

cnf(c_2143,plain,
    ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2125])).

cnf(c_2159,plain,
    ( m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2119])).

cnf(c_2161,plain,
    ( m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2159])).

cnf(c_13,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_652,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_34])).

cnf(c_653,plain,
    ( ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | v9_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_124,plain,
    ( ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6)
    | v9_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_655,plain,
    ( v9_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_35,c_34,c_32,c_124])).

cnf(c_717,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_655])).

cnf(c_718,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ r3_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v6_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_3,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_121,plain,
    ( v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_722,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ r3_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_35,c_34,c_32,c_118,c_121])).

cnf(c_723,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ r3_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_722])).

cnf(c_15,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_669,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_655])).

cnf(c_670,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_lattices(sK6,X0,X1)
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_35,c_34,c_32,c_121])).

cnf(c_675,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_674])).

cnf(c_812,plain,
    ( ~ r3_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k2_lattices(sK6,X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_723,c_675])).

cnf(c_2118,plain,
    ( ~ r3_lattices(sK6,X0_56,X1_56)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | k2_lattices(sK6,X0_56,X1_56) = X0_56 ),
    inference(subtyping,[status(esa)],[c_812])).

cnf(c_2607,plain,
    ( ~ r3_lattices(sK6,k15_lattice3(sK6,X0_59),X0_56)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6))
    | k2_lattices(sK6,k15_lattice3(sK6,X0_59),X0_56) = k15_lattice3(sK6,X0_59) ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_2868,plain,
    ( ~ r3_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6))
    | ~ m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) = k15_lattice3(sK6,X0_59) ),
    inference(instantiation,[status(thm)],[c_2607])).

cnf(c_2869,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) = k15_lattice3(sK6,X0_59)
    | r3_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) != iProver_top
    | m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2868])).

cnf(c_2871,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) = k15_lattice3(sK6,k1_xboole_0)
    | r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) != iProver_top
    | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_2127,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_2981,plain,
    ( k5_lattices(sK6) = k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1128,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_35])).

cnf(c_1129,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,X0,k5_lattices(sK6)) = k5_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_1128])).

cnf(c_102,plain,
    ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1133,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,X0,k5_lattices(sK6)) = k5_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1129,c_35,c_32,c_99,c_102])).

cnf(c_2108,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | ~ v13_lattices(sK6)
    | k2_lattices(sK6,X0_56,k5_lattices(sK6)) = k5_lattices(sK6) ),
    inference(subtyping,[status(esa)],[c_1133])).

cnf(c_2508,plain,
    ( k2_lattices(sK6,X0_56,k5_lattices(sK6)) = k5_lattices(sK6)
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2108])).

cnf(c_2988,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) = k5_lattices(sK6)
    | v13_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_2508])).

cnf(c_2991,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) = k5_lattices(sK6)
    | v13_lattices(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2988])).

cnf(c_991,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_992,plain,
    ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | ~ l1_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_991])).

cnf(c_994,plain,
    ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_992,c_35,c_32,c_99,c_102])).

cnf(c_2114,plain,
    ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_994])).

cnf(c_2502,plain,
    ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2114])).

cnf(c_2677,plain,
    ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),k5_lattices(sK6))) = k5_lattices(sK6) ),
    inference(superposition,[status(thm)],[c_2502,c_2493])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_403,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_404,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_29,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK5(X0,X1,X2),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_500,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK5(X0,X1,X2),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_501,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
    | r2_hidden(sK5(sK6,X0,X1),X0)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_505,plain,
    ( r2_hidden(sK5(sK6,X0,X1),X0)
    | r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_35,c_34,c_32])).

cnf(c_506,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
    | r2_hidden(sK5(sK6,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_505])).

cnf(c_615,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
    | sK5(sK6,X0,X1) != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_404,c_506])).

cnf(c_616,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0)) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_2120,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_59)) ),
    inference(subtyping,[status(esa)],[c_616])).

cnf(c_2496,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_59)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2120])).

cnf(c_3273,plain,
    ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2496])).

cnf(c_2129,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_3241,plain,
    ( X0_56 != X1_56
    | k15_lattice3(sK6,X0_59) != X1_56
    | k15_lattice3(sK6,X0_59) = X0_56 ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_3894,plain,
    ( X0_56 != k15_lattice3(sK6,X0_59)
    | k15_lattice3(sK6,X0_59) = X0_56
    | k15_lattice3(sK6,X0_59) != k15_lattice3(sK6,X0_59) ),
    inference(instantiation,[status(thm)],[c_3241])).

cnf(c_4616,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) != k15_lattice3(sK6,X0_59)
    | k15_lattice3(sK6,X0_59) = k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6))
    | k15_lattice3(sK6,X0_59) != k15_lattice3(sK6,X0_59) ),
    inference(instantiation,[status(thm)],[c_3894])).

cnf(c_4617,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) != k15_lattice3(sK6,k1_xboole_0)
    | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6))
    | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4616])).

cnf(c_2674,plain,
    ( X0_56 != X1_56
    | k5_lattices(sK6) != X1_56
    | k5_lattices(sK6) = X0_56 ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_3158,plain,
    ( X0_56 != k5_lattices(sK6)
    | k5_lattices(sK6) = X0_56
    | k5_lattices(sK6) != k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_2674])).

cnf(c_5593,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) != k5_lattices(sK6)
    | k5_lattices(sK6) = k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6))
    | k5_lattices(sK6) != k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_3158])).

cnf(c_5599,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) != k5_lattices(sK6)
    | k5_lattices(sK6) = k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6))
    | k5_lattices(sK6) != k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_5593])).

cnf(c_2637,plain,
    ( k15_lattice3(sK6,k1_xboole_0) != X0_56
    | k5_lattices(sK6) != X0_56
    | k5_lattices(sK6) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_12411,plain,
    ( k15_lattice3(sK6,k1_xboole_0) != k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6))
    | k5_lattices(sK6) != k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6))
    | k5_lattices(sK6) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_12509,plain,
    ( m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | k2_lattices(sK6,sK1(sK6,X0_56),sK1(sK6,k15_lattice3(sK6,X0_59))) = k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),sK1(sK6,X0_56)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12362,c_36,c_39,c_100,c_103,c_2138,c_2142,c_2143,c_2161,c_2871,c_2981,c_2991,c_3273,c_4617,c_5599,c_12411])).

cnf(c_12510,plain,
    ( k2_lattices(sK6,sK1(sK6,X0_56),sK1(sK6,k15_lattice3(sK6,X0_59))) = k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),sK1(sK6,X0_56))
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12509])).

cnf(c_12515,plain,
    ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),sK1(sK6,sK2(sK6))) = k2_lattices(sK6,sK1(sK6,sK2(sK6)),sK1(sK6,k15_lattice3(sK6,X0_59)))
    | v13_lattices(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2501,c_12510])).

cnf(c_12670,plain,
    ( v13_lattices(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12515,c_36,c_39,c_100,c_103,c_2138,c_2142,c_2143,c_2161,c_2871,c_2981,c_2991,c_3273,c_4617,c_5599,c_12411])).

cnf(c_12696,plain,
    ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK1(sK6,k15_lattice3(sK6,X0_59)))) = sK1(sK6,k15_lattice3(sK6,X0_59)) ),
    inference(superposition,[status(thm)],[c_4639,c_12670])).

cnf(c_2498,plain,
    ( k2_lattices(sK6,X0_56,X1_56) = X0_56
    | r3_lattices(sK6,X0_56,X1_56) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2118])).

cnf(c_3924,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_59)) = k15_lattice3(sK6,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2496,c_2498])).

cnf(c_8125,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_59)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3924,c_2159,c_2161])).

cnf(c_23276,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,X0_59))) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12696,c_8125])).

cnf(c_23429,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_23276])).

cnf(c_2996,plain,
    ( k2_lattices(sK6,X0_56,k15_lattice3(sK6,X0_59)) = k2_lattices(sK6,k15_lattice3(sK6,X0_59),X0_56)
    | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_2500])).

cnf(c_4146,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k15_lattice3(sK6,X1_59)) = k2_lattices(sK6,k15_lattice3(sK6,X1_59),k15_lattice3(sK6,X0_59)) ),
    inference(superposition,[status(thm)],[c_2497,c_2996])).

cnf(c_8133,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8125,c_4146])).

cnf(c_23240,plain,
    ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12696,c_8133])).

cnf(c_23400,plain,
    ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_23240])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1083,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_1084,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | v13_lattices(sK6)
    | k2_lattices(sK6,X0,sK1(sK6,X0)) != X0
    | k2_lattices(sK6,sK1(sK6,X0),X0) != X0 ),
    inference(unflattening,[status(thm)],[c_1083])).

cnf(c_1088,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v13_lattices(sK6)
    | k2_lattices(sK6,X0,sK1(sK6,X0)) != X0
    | k2_lattices(sK6,sK1(sK6,X0),X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1084,c_32,c_99])).

cnf(c_2110,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
    | v13_lattices(sK6)
    | k2_lattices(sK6,X0_56,sK1(sK6,X0_56)) != X0_56
    | k2_lattices(sK6,sK1(sK6,X0_56),X0_56) != X0_56 ),
    inference(subtyping,[status(esa)],[c_1088])).

cnf(c_2585,plain,
    ( ~ m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6))
    | v13_lattices(sK6)
    | k2_lattices(sK6,k15_lattice3(sK6,X0_59),sK1(sK6,k15_lattice3(sK6,X0_59))) != k15_lattice3(sK6,X0_59)
    | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),k15_lattice3(sK6,X0_59)) != k15_lattice3(sK6,X0_59) ),
    inference(instantiation,[status(thm)],[c_2110])).

cnf(c_2586,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),sK1(sK6,k15_lattice3(sK6,X0_59))) != k15_lattice3(sK6,X0_59)
    | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),k15_lattice3(sK6,X0_59)) != k15_lattice3(sK6,X0_59)
    | m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2585])).

cnf(c_2588,plain,
    ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) != k15_lattice3(sK6,k1_xboole_0)
    | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) != k15_lattice3(sK6,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v13_lattices(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2586])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23429,c_23400,c_12670,c_2588,c_2161])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:06:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.99/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.99/1.49  
% 7.99/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.99/1.49  
% 7.99/1.49  ------  iProver source info
% 7.99/1.49  
% 7.99/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.99/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.99/1.49  git: non_committed_changes: false
% 7.99/1.49  git: last_make_outside_of_git: false
% 7.99/1.49  
% 7.99/1.49  ------ 
% 7.99/1.49  
% 7.99/1.49  ------ Input Options
% 7.99/1.49  
% 7.99/1.49  --out_options                           all
% 7.99/1.49  --tptp_safe_out                         true
% 7.99/1.49  --problem_path                          ""
% 7.99/1.49  --include_path                          ""
% 7.99/1.49  --clausifier                            res/vclausify_rel
% 7.99/1.49  --clausifier_options                    ""
% 7.99/1.49  --stdin                                 false
% 7.99/1.49  --stats_out                             all
% 7.99/1.49  
% 7.99/1.49  ------ General Options
% 7.99/1.49  
% 7.99/1.49  --fof                                   false
% 7.99/1.49  --time_out_real                         305.
% 7.99/1.49  --time_out_virtual                      -1.
% 7.99/1.49  --symbol_type_check                     false
% 7.99/1.49  --clausify_out                          false
% 7.99/1.49  --sig_cnt_out                           false
% 7.99/1.49  --trig_cnt_out                          false
% 7.99/1.49  --trig_cnt_out_tolerance                1.
% 7.99/1.49  --trig_cnt_out_sk_spl                   false
% 7.99/1.49  --abstr_cl_out                          false
% 7.99/1.49  
% 7.99/1.49  ------ Global Options
% 7.99/1.49  
% 7.99/1.49  --schedule                              default
% 7.99/1.49  --add_important_lit                     false
% 7.99/1.49  --prop_solver_per_cl                    1000
% 7.99/1.49  --min_unsat_core                        false
% 7.99/1.49  --soft_assumptions                      false
% 7.99/1.49  --soft_lemma_size                       3
% 7.99/1.49  --prop_impl_unit_size                   0
% 7.99/1.49  --prop_impl_unit                        []
% 7.99/1.49  --share_sel_clauses                     true
% 7.99/1.49  --reset_solvers                         false
% 7.99/1.49  --bc_imp_inh                            [conj_cone]
% 7.99/1.49  --conj_cone_tolerance                   3.
% 7.99/1.49  --extra_neg_conj                        none
% 7.99/1.49  --large_theory_mode                     true
% 7.99/1.49  --prolific_symb_bound                   200
% 7.99/1.49  --lt_threshold                          2000
% 7.99/1.49  --clause_weak_htbl                      true
% 7.99/1.49  --gc_record_bc_elim                     false
% 7.99/1.49  
% 7.99/1.49  ------ Preprocessing Options
% 7.99/1.49  
% 7.99/1.49  --preprocessing_flag                    true
% 7.99/1.49  --time_out_prep_mult                    0.1
% 7.99/1.49  --splitting_mode                        input
% 7.99/1.49  --splitting_grd                         true
% 7.99/1.49  --splitting_cvd                         false
% 7.99/1.49  --splitting_cvd_svl                     false
% 7.99/1.49  --splitting_nvd                         32
% 7.99/1.49  --sub_typing                            true
% 7.99/1.49  --prep_gs_sim                           true
% 7.99/1.49  --prep_unflatten                        true
% 7.99/1.49  --prep_res_sim                          true
% 7.99/1.49  --prep_upred                            true
% 7.99/1.49  --prep_sem_filter                       exhaustive
% 7.99/1.49  --prep_sem_filter_out                   false
% 7.99/1.49  --pred_elim                             true
% 7.99/1.49  --res_sim_input                         true
% 7.99/1.49  --eq_ax_congr_red                       true
% 7.99/1.49  --pure_diseq_elim                       true
% 7.99/1.49  --brand_transform                       false
% 7.99/1.49  --non_eq_to_eq                          false
% 7.99/1.49  --prep_def_merge                        true
% 7.99/1.49  --prep_def_merge_prop_impl              false
% 7.99/1.49  --prep_def_merge_mbd                    true
% 7.99/1.49  --prep_def_merge_tr_red                 false
% 7.99/1.49  --prep_def_merge_tr_cl                  false
% 7.99/1.49  --smt_preprocessing                     true
% 7.99/1.49  --smt_ac_axioms                         fast
% 7.99/1.49  --preprocessed_out                      false
% 7.99/1.49  --preprocessed_stats                    false
% 7.99/1.49  
% 7.99/1.49  ------ Abstraction refinement Options
% 7.99/1.49  
% 7.99/1.49  --abstr_ref                             []
% 7.99/1.49  --abstr_ref_prep                        false
% 7.99/1.49  --abstr_ref_until_sat                   false
% 7.99/1.49  --abstr_ref_sig_restrict                funpre
% 7.99/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.99/1.49  --abstr_ref_under                       []
% 7.99/1.49  
% 7.99/1.49  ------ SAT Options
% 7.99/1.49  
% 7.99/1.49  --sat_mode                              false
% 7.99/1.49  --sat_fm_restart_options                ""
% 7.99/1.49  --sat_gr_def                            false
% 7.99/1.49  --sat_epr_types                         true
% 7.99/1.49  --sat_non_cyclic_types                  false
% 7.99/1.49  --sat_finite_models                     false
% 7.99/1.49  --sat_fm_lemmas                         false
% 7.99/1.49  --sat_fm_prep                           false
% 7.99/1.49  --sat_fm_uc_incr                        true
% 7.99/1.49  --sat_out_model                         small
% 7.99/1.49  --sat_out_clauses                       false
% 7.99/1.49  
% 7.99/1.49  ------ QBF Options
% 7.99/1.49  
% 7.99/1.49  --qbf_mode                              false
% 7.99/1.49  --qbf_elim_univ                         false
% 7.99/1.49  --qbf_dom_inst                          none
% 7.99/1.49  --qbf_dom_pre_inst                      false
% 7.99/1.49  --qbf_sk_in                             false
% 7.99/1.49  --qbf_pred_elim                         true
% 7.99/1.49  --qbf_split                             512
% 7.99/1.49  
% 7.99/1.49  ------ BMC1 Options
% 7.99/1.49  
% 7.99/1.49  --bmc1_incremental                      false
% 7.99/1.49  --bmc1_axioms                           reachable_all
% 7.99/1.49  --bmc1_min_bound                        0
% 7.99/1.49  --bmc1_max_bound                        -1
% 7.99/1.49  --bmc1_max_bound_default                -1
% 7.99/1.49  --bmc1_symbol_reachability              true
% 7.99/1.49  --bmc1_property_lemmas                  false
% 7.99/1.49  --bmc1_k_induction                      false
% 7.99/1.49  --bmc1_non_equiv_states                 false
% 7.99/1.49  --bmc1_deadlock                         false
% 7.99/1.49  --bmc1_ucm                              false
% 7.99/1.49  --bmc1_add_unsat_core                   none
% 7.99/1.49  --bmc1_unsat_core_children              false
% 7.99/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.99/1.49  --bmc1_out_stat                         full
% 7.99/1.49  --bmc1_ground_init                      false
% 7.99/1.49  --bmc1_pre_inst_next_state              false
% 7.99/1.49  --bmc1_pre_inst_state                   false
% 7.99/1.49  --bmc1_pre_inst_reach_state             false
% 7.99/1.49  --bmc1_out_unsat_core                   false
% 7.99/1.49  --bmc1_aig_witness_out                  false
% 7.99/1.49  --bmc1_verbose                          false
% 7.99/1.49  --bmc1_dump_clauses_tptp                false
% 7.99/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.99/1.49  --bmc1_dump_file                        -
% 7.99/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.99/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.99/1.49  --bmc1_ucm_extend_mode                  1
% 7.99/1.49  --bmc1_ucm_init_mode                    2
% 7.99/1.49  --bmc1_ucm_cone_mode                    none
% 7.99/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.99/1.49  --bmc1_ucm_relax_model                  4
% 7.99/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.99/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.99/1.49  --bmc1_ucm_layered_model                none
% 7.99/1.49  --bmc1_ucm_max_lemma_size               10
% 7.99/1.49  
% 7.99/1.49  ------ AIG Options
% 7.99/1.49  
% 7.99/1.49  --aig_mode                              false
% 7.99/1.49  
% 7.99/1.49  ------ Instantiation Options
% 7.99/1.49  
% 7.99/1.49  --instantiation_flag                    true
% 7.99/1.49  --inst_sos_flag                         true
% 7.99/1.49  --inst_sos_phase                        true
% 7.99/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.99/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.99/1.49  --inst_lit_sel_side                     num_symb
% 7.99/1.49  --inst_solver_per_active                1400
% 7.99/1.49  --inst_solver_calls_frac                1.
% 7.99/1.49  --inst_passive_queue_type               priority_queues
% 7.99/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.99/1.49  --inst_passive_queues_freq              [25;2]
% 7.99/1.49  --inst_dismatching                      true
% 7.99/1.49  --inst_eager_unprocessed_to_passive     true
% 7.99/1.49  --inst_prop_sim_given                   true
% 7.99/1.49  --inst_prop_sim_new                     false
% 7.99/1.49  --inst_subs_new                         false
% 7.99/1.49  --inst_eq_res_simp                      false
% 7.99/1.49  --inst_subs_given                       false
% 7.99/1.49  --inst_orphan_elimination               true
% 7.99/1.49  --inst_learning_loop_flag               true
% 7.99/1.49  --inst_learning_start                   3000
% 7.99/1.49  --inst_learning_factor                  2
% 7.99/1.49  --inst_start_prop_sim_after_learn       3
% 7.99/1.49  --inst_sel_renew                        solver
% 7.99/1.49  --inst_lit_activity_flag                true
% 7.99/1.49  --inst_restr_to_given                   false
% 7.99/1.49  --inst_activity_threshold               500
% 7.99/1.49  --inst_out_proof                        true
% 7.99/1.49  
% 7.99/1.49  ------ Resolution Options
% 7.99/1.49  
% 7.99/1.49  --resolution_flag                       true
% 7.99/1.49  --res_lit_sel                           adaptive
% 7.99/1.49  --res_lit_sel_side                      none
% 7.99/1.49  --res_ordering                          kbo
% 7.99/1.49  --res_to_prop_solver                    active
% 7.99/1.49  --res_prop_simpl_new                    false
% 7.99/1.49  --res_prop_simpl_given                  true
% 7.99/1.49  --res_passive_queue_type                priority_queues
% 7.99/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.99/1.49  --res_passive_queues_freq               [15;5]
% 7.99/1.49  --res_forward_subs                      full
% 7.99/1.49  --res_backward_subs                     full
% 7.99/1.49  --res_forward_subs_resolution           true
% 7.99/1.49  --res_backward_subs_resolution          true
% 7.99/1.49  --res_orphan_elimination                true
% 7.99/1.49  --res_time_limit                        2.
% 7.99/1.49  --res_out_proof                         true
% 7.99/1.49  
% 7.99/1.49  ------ Superposition Options
% 7.99/1.49  
% 7.99/1.49  --superposition_flag                    true
% 7.99/1.49  --sup_passive_queue_type                priority_queues
% 7.99/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.99/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.99/1.49  --demod_completeness_check              fast
% 7.99/1.49  --demod_use_ground                      true
% 7.99/1.49  --sup_to_prop_solver                    passive
% 7.99/1.49  --sup_prop_simpl_new                    true
% 7.99/1.49  --sup_prop_simpl_given                  true
% 7.99/1.49  --sup_fun_splitting                     true
% 7.99/1.49  --sup_smt_interval                      50000
% 7.99/1.49  
% 7.99/1.49  ------ Superposition Simplification Setup
% 7.99/1.49  
% 7.99/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.99/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.99/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.99/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.99/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.99/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.99/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.99/1.49  --sup_immed_triv                        [TrivRules]
% 7.99/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.99/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.99/1.49  --sup_immed_bw_main                     []
% 7.99/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.99/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.99/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.99/1.49  --sup_input_bw                          []
% 7.99/1.49  
% 7.99/1.49  ------ Combination Options
% 7.99/1.49  
% 7.99/1.49  --comb_res_mult                         3
% 7.99/1.49  --comb_sup_mult                         2
% 7.99/1.49  --comb_inst_mult                        10
% 7.99/1.49  
% 7.99/1.49  ------ Debug Options
% 7.99/1.49  
% 7.99/1.49  --dbg_backtrace                         false
% 7.99/1.49  --dbg_dump_prop_clauses                 false
% 7.99/1.49  --dbg_dump_prop_clauses_file            -
% 7.99/1.49  --dbg_out_stat                          false
% 7.99/1.49  ------ Parsing...
% 7.99/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.99/1.49  
% 7.99/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.99/1.49  
% 7.99/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.99/1.49  
% 7.99/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.99/1.49  ------ Proving...
% 7.99/1.49  ------ Problem Properties 
% 7.99/1.49  
% 7.99/1.49  
% 7.99/1.49  clauses                                 20
% 7.99/1.49  conjectures                             1
% 7.99/1.49  EPR                                     0
% 7.99/1.49  Horn                                    16
% 7.99/1.49  unary                                   3
% 7.99/1.49  binary                                  5
% 7.99/1.49  lits                                    55
% 7.99/1.49  lits eq                                 16
% 7.99/1.49  fd_pure                                 0
% 7.99/1.49  fd_pseudo                               0
% 7.99/1.49  fd_cond                                 2
% 7.99/1.49  fd_pseudo_cond                          0
% 7.99/1.49  AC symbols                              0
% 7.99/1.49  
% 7.99/1.49  ------ Schedule dynamic 5 is on 
% 7.99/1.49  
% 7.99/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.99/1.49  
% 7.99/1.49  
% 7.99/1.49  ------ 
% 7.99/1.49  Current options:
% 7.99/1.49  ------ 
% 7.99/1.49  
% 7.99/1.49  ------ Input Options
% 7.99/1.49  
% 7.99/1.49  --out_options                           all
% 7.99/1.49  --tptp_safe_out                         true
% 7.99/1.49  --problem_path                          ""
% 7.99/1.49  --include_path                          ""
% 7.99/1.49  --clausifier                            res/vclausify_rel
% 7.99/1.49  --clausifier_options                    ""
% 7.99/1.49  --stdin                                 false
% 7.99/1.49  --stats_out                             all
% 7.99/1.49  
% 7.99/1.49  ------ General Options
% 7.99/1.49  
% 7.99/1.49  --fof                                   false
% 7.99/1.49  --time_out_real                         305.
% 7.99/1.49  --time_out_virtual                      -1.
% 7.99/1.49  --symbol_type_check                     false
% 7.99/1.49  --clausify_out                          false
% 7.99/1.49  --sig_cnt_out                           false
% 7.99/1.49  --trig_cnt_out                          false
% 7.99/1.49  --trig_cnt_out_tolerance                1.
% 7.99/1.49  --trig_cnt_out_sk_spl                   false
% 7.99/1.49  --abstr_cl_out                          false
% 7.99/1.49  
% 7.99/1.49  ------ Global Options
% 7.99/1.49  
% 7.99/1.49  --schedule                              default
% 7.99/1.49  --add_important_lit                     false
% 7.99/1.49  --prop_solver_per_cl                    1000
% 7.99/1.49  --min_unsat_core                        false
% 7.99/1.49  --soft_assumptions                      false
% 7.99/1.49  --soft_lemma_size                       3
% 7.99/1.49  --prop_impl_unit_size                   0
% 7.99/1.49  --prop_impl_unit                        []
% 7.99/1.49  --share_sel_clauses                     true
% 7.99/1.49  --reset_solvers                         false
% 7.99/1.49  --bc_imp_inh                            [conj_cone]
% 7.99/1.49  --conj_cone_tolerance                   3.
% 7.99/1.49  --extra_neg_conj                        none
% 7.99/1.49  --large_theory_mode                     true
% 7.99/1.49  --prolific_symb_bound                   200
% 7.99/1.49  --lt_threshold                          2000
% 7.99/1.49  --clause_weak_htbl                      true
% 7.99/1.49  --gc_record_bc_elim                     false
% 7.99/1.49  
% 7.99/1.49  ------ Preprocessing Options
% 7.99/1.49  
% 7.99/1.49  --preprocessing_flag                    true
% 7.99/1.49  --time_out_prep_mult                    0.1
% 7.99/1.49  --splitting_mode                        input
% 7.99/1.49  --splitting_grd                         true
% 7.99/1.49  --splitting_cvd                         false
% 7.99/1.49  --splitting_cvd_svl                     false
% 7.99/1.49  --splitting_nvd                         32
% 7.99/1.49  --sub_typing                            true
% 7.99/1.49  --prep_gs_sim                           true
% 7.99/1.49  --prep_unflatten                        true
% 7.99/1.49  --prep_res_sim                          true
% 7.99/1.49  --prep_upred                            true
% 7.99/1.49  --prep_sem_filter                       exhaustive
% 7.99/1.49  --prep_sem_filter_out                   false
% 7.99/1.49  --pred_elim                             true
% 7.99/1.49  --res_sim_input                         true
% 7.99/1.49  --eq_ax_congr_red                       true
% 7.99/1.49  --pure_diseq_elim                       true
% 7.99/1.49  --brand_transform                       false
% 7.99/1.49  --non_eq_to_eq                          false
% 7.99/1.49  --prep_def_merge                        true
% 7.99/1.49  --prep_def_merge_prop_impl              false
% 7.99/1.49  --prep_def_merge_mbd                    true
% 7.99/1.49  --prep_def_merge_tr_red                 false
% 7.99/1.49  --prep_def_merge_tr_cl                  false
% 7.99/1.49  --smt_preprocessing                     true
% 7.99/1.49  --smt_ac_axioms                         fast
% 7.99/1.49  --preprocessed_out                      false
% 7.99/1.49  --preprocessed_stats                    false
% 7.99/1.49  
% 7.99/1.49  ------ Abstraction refinement Options
% 7.99/1.49  
% 7.99/1.49  --abstr_ref                             []
% 7.99/1.49  --abstr_ref_prep                        false
% 7.99/1.49  --abstr_ref_until_sat                   false
% 7.99/1.49  --abstr_ref_sig_restrict                funpre
% 7.99/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.99/1.49  --abstr_ref_under                       []
% 7.99/1.49  
% 7.99/1.49  ------ SAT Options
% 7.99/1.49  
% 7.99/1.49  --sat_mode                              false
% 7.99/1.49  --sat_fm_restart_options                ""
% 7.99/1.49  --sat_gr_def                            false
% 7.99/1.49  --sat_epr_types                         true
% 7.99/1.49  --sat_non_cyclic_types                  false
% 7.99/1.49  --sat_finite_models                     false
% 7.99/1.49  --sat_fm_lemmas                         false
% 7.99/1.49  --sat_fm_prep                           false
% 7.99/1.49  --sat_fm_uc_incr                        true
% 7.99/1.49  --sat_out_model                         small
% 7.99/1.49  --sat_out_clauses                       false
% 7.99/1.49  
% 7.99/1.49  ------ QBF Options
% 7.99/1.49  
% 7.99/1.49  --qbf_mode                              false
% 7.99/1.49  --qbf_elim_univ                         false
% 7.99/1.49  --qbf_dom_inst                          none
% 7.99/1.49  --qbf_dom_pre_inst                      false
% 7.99/1.49  --qbf_sk_in                             false
% 7.99/1.49  --qbf_pred_elim                         true
% 7.99/1.49  --qbf_split                             512
% 7.99/1.49  
% 7.99/1.49  ------ BMC1 Options
% 7.99/1.49  
% 7.99/1.49  --bmc1_incremental                      false
% 7.99/1.49  --bmc1_axioms                           reachable_all
% 7.99/1.49  --bmc1_min_bound                        0
% 7.99/1.49  --bmc1_max_bound                        -1
% 7.99/1.49  --bmc1_max_bound_default                -1
% 7.99/1.49  --bmc1_symbol_reachability              true
% 7.99/1.49  --bmc1_property_lemmas                  false
% 7.99/1.49  --bmc1_k_induction                      false
% 7.99/1.49  --bmc1_non_equiv_states                 false
% 7.99/1.49  --bmc1_deadlock                         false
% 7.99/1.49  --bmc1_ucm                              false
% 7.99/1.49  --bmc1_add_unsat_core                   none
% 7.99/1.49  --bmc1_unsat_core_children              false
% 7.99/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.99/1.49  --bmc1_out_stat                         full
% 7.99/1.49  --bmc1_ground_init                      false
% 7.99/1.49  --bmc1_pre_inst_next_state              false
% 7.99/1.49  --bmc1_pre_inst_state                   false
% 7.99/1.49  --bmc1_pre_inst_reach_state             false
% 7.99/1.49  --bmc1_out_unsat_core                   false
% 7.99/1.49  --bmc1_aig_witness_out                  false
% 7.99/1.49  --bmc1_verbose                          false
% 7.99/1.49  --bmc1_dump_clauses_tptp                false
% 7.99/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.99/1.49  --bmc1_dump_file                        -
% 7.99/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.99/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.99/1.49  --bmc1_ucm_extend_mode                  1
% 7.99/1.49  --bmc1_ucm_init_mode                    2
% 7.99/1.49  --bmc1_ucm_cone_mode                    none
% 7.99/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.99/1.49  --bmc1_ucm_relax_model                  4
% 7.99/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.99/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.99/1.49  --bmc1_ucm_layered_model                none
% 7.99/1.49  --bmc1_ucm_max_lemma_size               10
% 7.99/1.49  
% 7.99/1.49  ------ AIG Options
% 7.99/1.49  
% 7.99/1.49  --aig_mode                              false
% 7.99/1.49  
% 7.99/1.49  ------ Instantiation Options
% 7.99/1.49  
% 7.99/1.49  --instantiation_flag                    true
% 7.99/1.49  --inst_sos_flag                         true
% 7.99/1.49  --inst_sos_phase                        true
% 7.99/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.99/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.99/1.49  --inst_lit_sel_side                     none
% 7.99/1.49  --inst_solver_per_active                1400
% 7.99/1.49  --inst_solver_calls_frac                1.
% 7.99/1.49  --inst_passive_queue_type               priority_queues
% 7.99/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.99/1.49  --inst_passive_queues_freq              [25;2]
% 7.99/1.49  --inst_dismatching                      true
% 7.99/1.49  --inst_eager_unprocessed_to_passive     true
% 7.99/1.49  --inst_prop_sim_given                   true
% 7.99/1.49  --inst_prop_sim_new                     false
% 7.99/1.49  --inst_subs_new                         false
% 7.99/1.49  --inst_eq_res_simp                      false
% 7.99/1.49  --inst_subs_given                       false
% 7.99/1.49  --inst_orphan_elimination               true
% 7.99/1.49  --inst_learning_loop_flag               true
% 7.99/1.49  --inst_learning_start                   3000
% 7.99/1.49  --inst_learning_factor                  2
% 7.99/1.49  --inst_start_prop_sim_after_learn       3
% 7.99/1.49  --inst_sel_renew                        solver
% 7.99/1.49  --inst_lit_activity_flag                true
% 7.99/1.49  --inst_restr_to_given                   false
% 7.99/1.49  --inst_activity_threshold               500
% 7.99/1.49  --inst_out_proof                        true
% 7.99/1.49  
% 7.99/1.49  ------ Resolution Options
% 7.99/1.49  
% 7.99/1.49  --resolution_flag                       false
% 7.99/1.49  --res_lit_sel                           adaptive
% 7.99/1.49  --res_lit_sel_side                      none
% 7.99/1.49  --res_ordering                          kbo
% 7.99/1.49  --res_to_prop_solver                    active
% 7.99/1.49  --res_prop_simpl_new                    false
% 7.99/1.49  --res_prop_simpl_given                  true
% 7.99/1.49  --res_passive_queue_type                priority_queues
% 7.99/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.99/1.49  --res_passive_queues_freq               [15;5]
% 7.99/1.49  --res_forward_subs                      full
% 7.99/1.49  --res_backward_subs                     full
% 7.99/1.49  --res_forward_subs_resolution           true
% 7.99/1.49  --res_backward_subs_resolution          true
% 7.99/1.49  --res_orphan_elimination                true
% 7.99/1.49  --res_time_limit                        2.
% 7.99/1.49  --res_out_proof                         true
% 7.99/1.49  
% 7.99/1.49  ------ Superposition Options
% 7.99/1.49  
% 7.99/1.49  --superposition_flag                    true
% 7.99/1.49  --sup_passive_queue_type                priority_queues
% 7.99/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.99/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.99/1.49  --demod_completeness_check              fast
% 7.99/1.49  --demod_use_ground                      true
% 7.99/1.49  --sup_to_prop_solver                    passive
% 7.99/1.49  --sup_prop_simpl_new                    true
% 7.99/1.49  --sup_prop_simpl_given                  true
% 7.99/1.49  --sup_fun_splitting                     true
% 7.99/1.49  --sup_smt_interval                      50000
% 7.99/1.49  
% 7.99/1.49  ------ Superposition Simplification Setup
% 7.99/1.49  
% 7.99/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.99/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.99/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.99/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.99/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.99/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.99/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.99/1.49  --sup_immed_triv                        [TrivRules]
% 7.99/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.99/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.99/1.49  --sup_immed_bw_main                     []
% 7.99/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.99/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.99/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.99/1.49  --sup_input_bw                          []
% 7.99/1.49  
% 7.99/1.49  ------ Combination Options
% 7.99/1.49  
% 7.99/1.49  --comb_res_mult                         3
% 7.99/1.49  --comb_sup_mult                         2
% 7.99/1.49  --comb_inst_mult                        10
% 7.99/1.49  
% 7.99/1.49  ------ Debug Options
% 7.99/1.49  
% 7.99/1.49  --dbg_backtrace                         false
% 7.99/1.49  --dbg_dump_prop_clauses                 false
% 7.99/1.49  --dbg_dump_prop_clauses_file            -
% 7.99/1.49  --dbg_out_stat                          false
% 7.99/1.49  
% 7.99/1.49  
% 7.99/1.49  
% 7.99/1.49  
% 7.99/1.49  ------ Proving...
% 7.99/1.49  
% 7.99/1.49  
% 7.99/1.49  % SZS status Theorem for theBenchmark.p
% 7.99/1.49  
% 7.99/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.99/1.49  
% 7.99/1.49  fof(f11,axiom,(
% 7.99/1.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f36,plain,(
% 7.99/1.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f11])).
% 7.99/1.49  
% 7.99/1.49  fof(f37,plain,(
% 7.99/1.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f36])).
% 7.99/1.49  
% 7.99/1.49  fof(f89,plain,(
% 7.99/1.49    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f37])).
% 7.99/1.49  
% 7.99/1.49  fof(f14,conjecture,(
% 7.99/1.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f15,negated_conjecture,(
% 7.99/1.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.99/1.49    inference(negated_conjecture,[],[f14])).
% 7.99/1.49  
% 7.99/1.49  fof(f42,plain,(
% 7.99/1.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f15])).
% 7.99/1.49  
% 7.99/1.49  fof(f43,plain,(
% 7.99/1.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f42])).
% 7.99/1.49  
% 7.99/1.49  fof(f62,plain,(
% 7.99/1.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) | ~l3_lattices(sK6) | ~v13_lattices(sK6) | ~v10_lattices(sK6) | v2_struct_0(sK6)) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6))),
% 7.99/1.49    introduced(choice_axiom,[])).
% 7.99/1.49  
% 7.99/1.49  fof(f63,plain,(
% 7.99/1.49    (k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) | ~l3_lattices(sK6) | ~v13_lattices(sK6) | ~v10_lattices(sK6) | v2_struct_0(sK6)) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6)),
% 7.99/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f62])).
% 7.99/1.49  
% 7.99/1.49  fof(f98,plain,(
% 7.99/1.49    l3_lattices(sK6)),
% 7.99/1.49    inference(cnf_transformation,[],[f63])).
% 7.99/1.49  
% 7.99/1.49  fof(f95,plain,(
% 7.99/1.49    ~v2_struct_0(sK6)),
% 7.99/1.49    inference(cnf_transformation,[],[f63])).
% 7.99/1.49  
% 7.99/1.49  fof(f9,axiom,(
% 7.99/1.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f32,plain,(
% 7.99/1.49    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f9])).
% 7.99/1.49  
% 7.99/1.49  fof(f33,plain,(
% 7.99/1.49    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f32])).
% 7.99/1.49  
% 7.99/1.49  fof(f50,plain,(
% 7.99/1.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(nnf_transformation,[],[f33])).
% 7.99/1.49  
% 7.99/1.49  fof(f51,plain,(
% 7.99/1.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(rectify,[],[f50])).
% 7.99/1.49  
% 7.99/1.49  fof(f53,plain,(
% 7.99/1.49    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 7.99/1.49    introduced(choice_axiom,[])).
% 7.99/1.49  
% 7.99/1.49  fof(f52,plain,(
% 7.99/1.49    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 7.99/1.49    introduced(choice_axiom,[])).
% 7.99/1.49  
% 7.99/1.49  fof(f54,plain,(
% 7.99/1.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f51,f53,f52])).
% 7.99/1.49  
% 7.99/1.49  fof(f83,plain,(
% 7.99/1.49    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f54])).
% 7.99/1.49  
% 7.99/1.49  fof(f6,axiom,(
% 7.99/1.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f16,plain,(
% 7.99/1.49    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 7.99/1.49    inference(pure_predicate_removal,[],[f6])).
% 7.99/1.49  
% 7.99/1.49  fof(f27,plain,(
% 7.99/1.49    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 7.99/1.49    inference(ennf_transformation,[],[f16])).
% 7.99/1.49  
% 7.99/1.49  fof(f75,plain,(
% 7.99/1.49    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f27])).
% 7.99/1.49  
% 7.99/1.49  fof(f12,axiom,(
% 7.99/1.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f38,plain,(
% 7.99/1.49    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f12])).
% 7.99/1.49  
% 7.99/1.49  fof(f39,plain,(
% 7.99/1.49    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f38])).
% 7.99/1.49  
% 7.99/1.49  fof(f90,plain,(
% 7.99/1.49    ( ! [X0,X1] : (k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f39])).
% 7.99/1.49  
% 7.99/1.49  fof(f97,plain,(
% 7.99/1.49    v4_lattice3(sK6)),
% 7.99/1.49    inference(cnf_transformation,[],[f63])).
% 7.99/1.49  
% 7.99/1.49  fof(f96,plain,(
% 7.99/1.49    v10_lattices(sK6)),
% 7.99/1.49    inference(cnf_transformation,[],[f63])).
% 7.99/1.49  
% 7.99/1.49  fof(f80,plain,(
% 7.99/1.49    ( ! [X0] : (m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f54])).
% 7.99/1.49  
% 7.99/1.49  fof(f10,axiom,(
% 7.99/1.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f34,plain,(
% 7.99/1.49    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f10])).
% 7.99/1.49  
% 7.99/1.49  fof(f35,plain,(
% 7.99/1.49    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f34])).
% 7.99/1.49  
% 7.99/1.49  fof(f55,plain,(
% 7.99/1.49    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(nnf_transformation,[],[f35])).
% 7.99/1.49  
% 7.99/1.49  fof(f56,plain,(
% 7.99/1.49    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(rectify,[],[f55])).
% 7.99/1.49  
% 7.99/1.49  fof(f58,plain,(
% 7.99/1.49    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK4(X0)) != k2_lattices(X0,sK4(X0),X1) & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 7.99/1.49    introduced(choice_axiom,[])).
% 7.99/1.49  
% 7.99/1.49  fof(f57,plain,(
% 7.99/1.49    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK3(X0)) != k2_lattices(X0,sK3(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 7.99/1.49    introduced(choice_axiom,[])).
% 7.99/1.49  
% 7.99/1.49  fof(f59,plain,(
% 7.99/1.49    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK3(X0),sK4(X0)) != k2_lattices(X0,sK4(X0),sK3(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).
% 7.99/1.49  
% 7.99/1.49  fof(f85,plain,(
% 7.99/1.49    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f59])).
% 7.99/1.49  
% 7.99/1.49  fof(f3,axiom,(
% 7.99/1.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f17,plain,(
% 7.99/1.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.99/1.49    inference(pure_predicate_removal,[],[f3])).
% 7.99/1.49  
% 7.99/1.49  fof(f18,plain,(
% 7.99/1.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.99/1.49    inference(pure_predicate_removal,[],[f17])).
% 7.99/1.49  
% 7.99/1.49  fof(f19,plain,(
% 7.99/1.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 7.99/1.49    inference(pure_predicate_removal,[],[f18])).
% 7.99/1.49  
% 7.99/1.49  fof(f21,plain,(
% 7.99/1.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 7.99/1.49    inference(ennf_transformation,[],[f19])).
% 7.99/1.49  
% 7.99/1.49  fof(f22,plain,(
% 7.99/1.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 7.99/1.49    inference(flattening,[],[f21])).
% 7.99/1.49  
% 7.99/1.49  fof(f67,plain,(
% 7.99/1.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f22])).
% 7.99/1.49  
% 7.99/1.49  fof(f5,axiom,(
% 7.99/1.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f25,plain,(
% 7.99/1.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f5])).
% 7.99/1.49  
% 7.99/1.49  fof(f26,plain,(
% 7.99/1.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f25])).
% 7.99/1.49  
% 7.99/1.49  fof(f74,plain,(
% 7.99/1.49    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f26])).
% 7.99/1.49  
% 7.99/1.49  fof(f99,plain,(
% 7.99/1.49    k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) | ~l3_lattices(sK6) | ~v13_lattices(sK6) | ~v10_lattices(sK6) | v2_struct_0(sK6)),
% 7.99/1.49    inference(cnf_transformation,[],[f63])).
% 7.99/1.49  
% 7.99/1.49  fof(f7,axiom,(
% 7.99/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f28,plain,(
% 7.99/1.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f7])).
% 7.99/1.49  
% 7.99/1.49  fof(f29,plain,(
% 7.99/1.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f28])).
% 7.99/1.49  
% 7.99/1.49  fof(f48,plain,(
% 7.99/1.49    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(nnf_transformation,[],[f29])).
% 7.99/1.49  
% 7.99/1.49  fof(f76,plain,(
% 7.99/1.49    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f48])).
% 7.99/1.49  
% 7.99/1.49  fof(f69,plain,(
% 7.99/1.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f22])).
% 7.99/1.49  
% 7.99/1.49  fof(f68,plain,(
% 7.99/1.49    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f22])).
% 7.99/1.49  
% 7.99/1.49  fof(f8,axiom,(
% 7.99/1.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f30,plain,(
% 7.99/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f8])).
% 7.99/1.49  
% 7.99/1.49  fof(f31,plain,(
% 7.99/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f30])).
% 7.99/1.49  
% 7.99/1.49  fof(f49,plain,(
% 7.99/1.49    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(nnf_transformation,[],[f31])).
% 7.99/1.49  
% 7.99/1.49  fof(f78,plain,(
% 7.99/1.49    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f49])).
% 7.99/1.49  
% 7.99/1.49  fof(f4,axiom,(
% 7.99/1.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f23,plain,(
% 7.99/1.49    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f4])).
% 7.99/1.49  
% 7.99/1.49  fof(f24,plain,(
% 7.99/1.49    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f23])).
% 7.99/1.49  
% 7.99/1.49  fof(f44,plain,(
% 7.99/1.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(nnf_transformation,[],[f24])).
% 7.99/1.49  
% 7.99/1.49  fof(f45,plain,(
% 7.99/1.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(rectify,[],[f44])).
% 7.99/1.49  
% 7.99/1.49  fof(f46,plain,(
% 7.99/1.49    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 7.99/1.49    introduced(choice_axiom,[])).
% 7.99/1.49  
% 7.99/1.49  fof(f47,plain,(
% 7.99/1.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 7.99/1.49  
% 7.99/1.49  fof(f71,plain,(
% 7.99/1.49    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f47])).
% 7.99/1.49  
% 7.99/1.49  fof(f100,plain,(
% 7.99/1.49    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(equality_resolution,[],[f71])).
% 7.99/1.49  
% 7.99/1.49  fof(f1,axiom,(
% 7.99/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f64,plain,(
% 7.99/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f1])).
% 7.99/1.49  
% 7.99/1.49  fof(f2,axiom,(
% 7.99/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f20,plain,(
% 7.99/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.99/1.49    inference(ennf_transformation,[],[f2])).
% 7.99/1.49  
% 7.99/1.49  fof(f65,plain,(
% 7.99/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f20])).
% 7.99/1.49  
% 7.99/1.49  fof(f13,axiom,(
% 7.99/1.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 7.99/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.49  
% 7.99/1.49  fof(f40,plain,(
% 7.99/1.49    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 7.99/1.49    inference(ennf_transformation,[],[f13])).
% 7.99/1.49  
% 7.99/1.49  fof(f41,plain,(
% 7.99/1.49    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(flattening,[],[f40])).
% 7.99/1.49  
% 7.99/1.49  fof(f60,plain,(
% 7.99/1.49    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK5(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 7.99/1.49    introduced(choice_axiom,[])).
% 7.99/1.49  
% 7.99/1.49  fof(f61,plain,(
% 7.99/1.49    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK5(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 7.99/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f60])).
% 7.99/1.49  
% 7.99/1.49  fof(f93,plain,(
% 7.99/1.49    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | r2_hidden(sK5(X0,X1,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f61])).
% 7.99/1.49  
% 7.99/1.49  fof(f84,plain,(
% 7.99/1.49    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.99/1.49    inference(cnf_transformation,[],[f54])).
% 7.99/1.49  
% 7.99/1.49  cnf(c_25,plain,
% 7.99/1.49      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_32,negated_conjecture,
% 7.99/1.49      ( l3_lattices(sK6) ),
% 7.99/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_785,plain,
% 7.99/1.49      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | sK6 != X0 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_786,plain,
% 7.99/1.49      ( m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6))
% 7.99/1.49      | v2_struct_0(sK6) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_785]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_35,negated_conjecture,
% 7.99/1.49      ( ~ v2_struct_0(sK6) ),
% 7.99/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_790,plain,
% 7.99/1.49      ( m1_subset_1(k15_lattice3(sK6,X0),u1_struct_0(sK6)) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_786,c_35]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2119,plain,
% 7.99/1.49      ( m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_790]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2497,plain,
% 7.99/1.49      ( m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) = iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2119]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_17,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 7.99/1.49      | ~ l1_lattices(X1)
% 7.99/1.49      | v13_lattices(X1)
% 7.99/1.49      | v2_struct_0(X1) ),
% 7.99/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1062,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 7.99/1.49      | ~ l1_lattices(X1)
% 7.99/1.49      | v13_lattices(X1)
% 7.99/1.49      | sK6 != X1 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1063,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
% 7.99/1.49      | ~ l1_lattices(sK6)
% 7.99/1.49      | v13_lattices(sK6) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_1062]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_11,plain,
% 7.99/1.49      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_99,plain,
% 7.99/1.49      ( l1_lattices(sK6) | ~ l3_lattices(sK6) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1067,plain,
% 7.99/1.49      ( m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | v13_lattices(sK6) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_1063,c_32,c_99]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1068,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | m1_subset_1(sK1(sK6,X0),u1_struct_0(sK6))
% 7.99/1.49      | v13_lattices(sK6) ),
% 7.99/1.49      inference(renaming,[status(thm)],[c_1067]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2111,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 7.99/1.49      | m1_subset_1(sK1(sK6,X0_56),u1_struct_0(sK6))
% 7.99/1.49      | v13_lattices(sK6) ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_1068]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2505,plain,
% 7.99/1.49      ( m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(sK1(sK6,X0_56),u1_struct_0(sK6)) = iProver_top
% 7.99/1.49      | v13_lattices(sK6) = iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2111]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_27,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | ~ v4_lattice3(X1)
% 7.99/1.49      | ~ l3_lattices(X1)
% 7.99/1.49      | v2_struct_0(X1)
% 7.99/1.49      | ~ v10_lattices(X1)
% 7.99/1.49      | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
% 7.99/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_33,negated_conjecture,
% 7.99/1.49      ( v4_lattice3(sK6) ),
% 7.99/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_542,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | ~ l3_lattices(X1)
% 7.99/1.49      | v2_struct_0(X1)
% 7.99/1.49      | ~ v10_lattices(X1)
% 7.99/1.49      | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0
% 7.99/1.49      | sK6 != X1 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_543,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ l3_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6)
% 7.99/1.49      | ~ v10_lattices(sK6)
% 7.99/1.49      | k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X0)) = X0 ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_542]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_34,negated_conjecture,
% 7.99/1.49      ( v10_lattices(sK6) ),
% 7.99/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_547,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X0)) = X0 ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_543,c_35,c_34,c_32]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2123,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 7.99/1.49      | k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X0_56)) = X0_56 ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_547]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2493,plain,
% 7.99/1.49      ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X0_56)) = X0_56
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2123]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_3192,plain,
% 7.99/1.49      ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK1(sK6,X0_56))) = sK1(sK6,X0_56)
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | v13_lattices(sK6) = iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2505,c_2493]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_4639,plain,
% 7.99/1.49      ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK1(sK6,k15_lattice3(sK6,X0_59)))) = sK1(sK6,k15_lattice3(sK6,X0_59))
% 7.99/1.49      | v13_lattices(sK6) = iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2497,c_3192]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_20,plain,
% 7.99/1.49      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
% 7.99/1.49      | ~ l1_lattices(X0)
% 7.99/1.49      | ~ v13_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_977,plain,
% 7.99/1.49      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
% 7.99/1.49      | ~ l1_lattices(X0)
% 7.99/1.49      | ~ v13_lattices(X0)
% 7.99/1.49      | sK6 != X0 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_978,plain,
% 7.99/1.49      ( m1_subset_1(sK2(sK6),u1_struct_0(sK6))
% 7.99/1.49      | ~ l1_lattices(sK6)
% 7.99/1.49      | ~ v13_lattices(sK6) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_977]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_980,plain,
% 7.99/1.49      ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) | ~ v13_lattices(sK6) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_978,c_32,c_99]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2115,plain,
% 7.99/1.49      ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) | ~ v13_lattices(sK6) ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_980]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2501,plain,
% 7.99/1.49      ( m1_subset_1(sK2(sK6),u1_struct_0(sK6)) = iProver_top
% 7.99/1.49      | v13_lattices(sK6) != iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2115]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_24,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.99/1.49      | ~ l1_lattices(X1)
% 7.99/1.49      | ~ v6_lattices(X1)
% 7.99/1.49      | v2_struct_0(X1)
% 7.99/1.49      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 7.99/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1002,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.99/1.49      | ~ l1_lattices(X1)
% 7.99/1.49      | ~ v6_lattices(X1)
% 7.99/1.49      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 7.99/1.49      | sK6 != X1 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1003,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | ~ l1_lattices(sK6)
% 7.99/1.49      | ~ v6_lattices(sK6)
% 7.99/1.49      | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_1002]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_4,plain,
% 7.99/1.49      ( v6_lattices(X0)
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | ~ v10_lattices(X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_630,plain,
% 7.99/1.49      ( v6_lattices(X0)
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | sK6 != X0 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_34]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_631,plain,
% 7.99/1.49      ( v6_lattices(sK6) | ~ l3_lattices(sK6) | v2_struct_0(sK6) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_630]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_118,plain,
% 7.99/1.49      ( v6_lattices(sK6)
% 7.99/1.49      | ~ l3_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6)
% 7.99/1.49      | ~ v10_lattices(sK6) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_633,plain,
% 7.99/1.49      ( v6_lattices(sK6) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_631,c_35,c_34,c_32,c_118]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_929,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.99/1.49      | ~ l1_lattices(X1)
% 7.99/1.49      | v2_struct_0(X1)
% 7.99/1.49      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 7.99/1.49      | sK6 != X1 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_633]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_930,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | ~ l1_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6)
% 7.99/1.49      | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_929]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_934,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_930,c_35,c_32,c_99]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1006,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | k2_lattices(sK6,X1,X0) = k2_lattices(sK6,X0,X1) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_1003,c_35,c_32,c_99,c_930]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2116,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 7.99/1.49      | k2_lattices(sK6,X1_56,X0_56) = k2_lattices(sK6,X0_56,X1_56) ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_1006]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2500,plain,
% 7.99/1.49      ( k2_lattices(sK6,X0_56,X1_56) = k2_lattices(sK6,X1_56,X0_56)
% 7.99/1.49      | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2116]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_3186,plain,
% 7.99/1.49      ( k2_lattices(sK6,X0_56,sK1(sK6,X1_56)) = k2_lattices(sK6,sK1(sK6,X1_56),X0_56)
% 7.99/1.49      | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | v13_lattices(sK6) = iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2505,c_2500]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_5835,plain,
% 7.99/1.49      ( k2_lattices(sK6,sK1(sK6,X0_56),sK1(sK6,X1_56)) = k2_lattices(sK6,sK1(sK6,X1_56),sK1(sK6,X0_56))
% 7.99/1.49      | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | v13_lattices(sK6) = iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2505,c_3186]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_12362,plain,
% 7.99/1.49      ( k2_lattices(sK6,sK1(sK6,X0_56),sK1(sK6,k15_lattice3(sK6,X0_59))) = k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),sK1(sK6,X0_56))
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | v13_lattices(sK6) = iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2497,c_5835]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_36,plain,
% 7.99/1.49      ( v2_struct_0(sK6) != iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_39,plain,
% 7.99/1.49      ( l3_lattices(sK6) = iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_98,plain,
% 7.99/1.49      ( l1_lattices(X0) = iProver_top | l3_lattices(X0) != iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_100,plain,
% 7.99/1.49      ( l1_lattices(sK6) = iProver_top
% 7.99/1.49      | l3_lattices(sK6) != iProver_top ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_98]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_10,plain,
% 7.99/1.49      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 7.99/1.49      | ~ l1_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_101,plain,
% 7.99/1.49      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) = iProver_top
% 7.99/1.49      | l1_lattices(X0) != iProver_top
% 7.99/1.49      | v2_struct_0(X0) = iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_103,plain,
% 7.99/1.49      ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) = iProver_top
% 7.99/1.49      | l1_lattices(sK6) != iProver_top
% 7.99/1.49      | v2_struct_0(sK6) = iProver_top ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_101]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2133,plain,
% 7.99/1.49      ( X0_59 != X1_59
% 7.99/1.49      | k15_lattice3(X0_58,X0_59) = k15_lattice3(X0_58,X1_59) ),
% 7.99/1.49      theory(equality) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2138,plain,
% 7.99/1.49      ( k1_xboole_0 != k1_xboole_0
% 7.99/1.49      | k15_lattice3(sK6,k1_xboole_0) = k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2133]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2128,plain,( X0_59 = X0_59 ),theory(equality) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2142,plain,
% 7.99/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2128]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_31,negated_conjecture,
% 7.99/1.49      ( ~ v13_lattices(sK6)
% 7.99/1.49      | ~ l3_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6)
% 7.99/1.49      | ~ v10_lattices(sK6)
% 7.99/1.49      | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_209,negated_conjecture,
% 7.99/1.49      ( ~ v13_lattices(sK6)
% 7.99/1.49      | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_31,c_35,c_34,c_32]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2125,negated_conjecture,
% 7.99/1.49      ( ~ v13_lattices(sK6)
% 7.99/1.49      | k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_209]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2143,plain,
% 7.99/1.49      ( k5_lattices(sK6) != k15_lattice3(sK6,k1_xboole_0)
% 7.99/1.49      | v13_lattices(sK6) != iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2125]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2159,plain,
% 7.99/1.49      ( m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) = iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2119]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2161,plain,
% 7.99/1.49      ( m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) = iProver_top ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2159]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_13,plain,
% 7.99/1.49      ( r1_lattices(X0,X1,X2)
% 7.99/1.49      | ~ r3_lattices(X0,X1,X2)
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.99/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.99/1.49      | ~ v6_lattices(X0)
% 7.99/1.49      | ~ v8_lattices(X0)
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | ~ v9_lattices(X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2,plain,
% 7.99/1.49      ( ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | ~ v10_lattices(X0)
% 7.99/1.49      | v9_lattices(X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_652,plain,
% 7.99/1.49      ( ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | v9_lattices(X0)
% 7.99/1.49      | sK6 != X0 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_2,c_34]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_653,plain,
% 7.99/1.49      ( ~ l3_lattices(sK6) | v2_struct_0(sK6) | v9_lattices(sK6) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_652]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_124,plain,
% 7.99/1.49      ( ~ l3_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6)
% 7.99/1.49      | ~ v10_lattices(sK6)
% 7.99/1.49      | v9_lattices(sK6) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_655,plain,
% 7.99/1.49      ( v9_lattices(sK6) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_653,c_35,c_34,c_32,c_124]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_717,plain,
% 7.99/1.49      ( r1_lattices(X0,X1,X2)
% 7.99/1.49      | ~ r3_lattices(X0,X1,X2)
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.99/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.99/1.49      | ~ v6_lattices(X0)
% 7.99/1.49      | ~ v8_lattices(X0)
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | sK6 != X0 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_655]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_718,plain,
% 7.99/1.49      ( r1_lattices(sK6,X0,X1)
% 7.99/1.49      | ~ r3_lattices(sK6,X0,X1)
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ v6_lattices(sK6)
% 7.99/1.49      | ~ v8_lattices(sK6)
% 7.99/1.49      | ~ l3_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_717]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_3,plain,
% 7.99/1.49      ( v8_lattices(X0)
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | ~ v10_lattices(X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_121,plain,
% 7.99/1.49      ( v8_lattices(sK6)
% 7.99/1.49      | ~ l3_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6)
% 7.99/1.49      | ~ v10_lattices(sK6) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_722,plain,
% 7.99/1.49      ( r1_lattices(sK6,X0,X1)
% 7.99/1.49      | ~ r3_lattices(sK6,X0,X1)
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_718,c_35,c_34,c_32,c_118,c_121]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_723,plain,
% 7.99/1.49      ( r1_lattices(sK6,X0,X1)
% 7.99/1.49      | ~ r3_lattices(sK6,X0,X1)
% 7.99/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 7.99/1.49      inference(renaming,[status(thm)],[c_722]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_15,plain,
% 7.99/1.49      ( ~ r1_lattices(X0,X1,X2)
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.99/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.99/1.49      | ~ v8_lattices(X0)
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | ~ v9_lattices(X0)
% 7.99/1.49      | k2_lattices(X0,X1,X2) = X1 ),
% 7.99/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_669,plain,
% 7.99/1.49      ( ~ r1_lattices(X0,X1,X2)
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.99/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.99/1.49      | ~ v8_lattices(X0)
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | k2_lattices(X0,X1,X2) = X1
% 7.99/1.49      | sK6 != X0 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_655]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_670,plain,
% 7.99/1.49      ( ~ r1_lattices(sK6,X0,X1)
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ v8_lattices(sK6)
% 7.99/1.49      | ~ l3_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6)
% 7.99/1.49      | k2_lattices(sK6,X0,X1) = X0 ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_669]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_674,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | ~ r1_lattices(sK6,X0,X1)
% 7.99/1.49      | k2_lattices(sK6,X0,X1) = X0 ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_670,c_35,c_34,c_32,c_121]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_675,plain,
% 7.99/1.49      ( ~ r1_lattices(sK6,X0,X1)
% 7.99/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | k2_lattices(sK6,X0,X1) = X0 ),
% 7.99/1.49      inference(renaming,[status(thm)],[c_674]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_812,plain,
% 7.99/1.49      ( ~ r3_lattices(sK6,X0,X1)
% 7.99/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.99/1.49      | k2_lattices(sK6,X0,X1) = X0 ),
% 7.99/1.49      inference(resolution,[status(thm)],[c_723,c_675]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2118,plain,
% 7.99/1.49      ( ~ r3_lattices(sK6,X0_56,X1_56)
% 7.99/1.49      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 7.99/1.49      | k2_lattices(sK6,X0_56,X1_56) = X0_56 ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_812]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2607,plain,
% 7.99/1.49      ( ~ r3_lattices(sK6,k15_lattice3(sK6,X0_59),X0_56)
% 7.99/1.49      | ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6))
% 7.99/1.49      | k2_lattices(sK6,k15_lattice3(sK6,X0_59),X0_56) = k15_lattice3(sK6,X0_59) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2118]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2868,plain,
% 7.99/1.49      ( ~ r3_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6))
% 7.99/1.49      | ~ m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.99/1.49      | k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) = k15_lattice3(sK6,X0_59) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2607]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2869,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) = k15_lattice3(sK6,X0_59)
% 7.99/1.49      | r3_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) != iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2868]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2871,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) = k15_lattice3(sK6,k1_xboole_0)
% 7.99/1.49      | r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) != iProver_top ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2869]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2127,plain,( X0_56 = X0_56 ),theory(equality) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2981,plain,
% 7.99/1.49      ( k5_lattices(sK6) = k5_lattices(sK6) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2127]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_8,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 7.99/1.49      | ~ l1_lattices(X1)
% 7.99/1.49      | ~ v13_lattices(X1)
% 7.99/1.49      | v2_struct_0(X1)
% 7.99/1.49      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1) ),
% 7.99/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1128,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 7.99/1.49      | ~ l1_lattices(X1)
% 7.99/1.49      | ~ v13_lattices(X1)
% 7.99/1.49      | k2_lattices(X1,X0,k5_lattices(X1)) = k5_lattices(X1)
% 7.99/1.49      | sK6 != X1 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_35]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1129,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.99/1.49      | ~ l1_lattices(sK6)
% 7.99/1.49      | ~ v13_lattices(sK6)
% 7.99/1.49      | k2_lattices(sK6,X0,k5_lattices(sK6)) = k5_lattices(sK6) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_1128]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_102,plain,
% 7.99/1.49      ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.99/1.49      | ~ l1_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1133,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ v13_lattices(sK6)
% 7.99/1.49      | k2_lattices(sK6,X0,k5_lattices(sK6)) = k5_lattices(sK6) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_1129,c_35,c_32,c_99,c_102]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2108,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 7.99/1.49      | ~ v13_lattices(sK6)
% 7.99/1.49      | k2_lattices(sK6,X0_56,k5_lattices(sK6)) = k5_lattices(sK6) ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_1133]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2508,plain,
% 7.99/1.49      ( k2_lattices(sK6,X0_56,k5_lattices(sK6)) = k5_lattices(sK6)
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | v13_lattices(sK6) != iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2108]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2988,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) = k5_lattices(sK6)
% 7.99/1.49      | v13_lattices(sK6) != iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2497,c_2508]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2991,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) = k5_lattices(sK6)
% 7.99/1.49      | v13_lattices(sK6) != iProver_top ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2988]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_991,plain,
% 7.99/1.49      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 7.99/1.49      | ~ l1_lattices(X0)
% 7.99/1.49      | sK6 != X0 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_992,plain,
% 7.99/1.49      ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.99/1.49      | ~ l1_lattices(sK6) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_991]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_994,plain,
% 7.99/1.49      ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_992,c_35,c_32,c_99,c_102]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2114,plain,
% 7.99/1.49      ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_994]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2502,plain,
% 7.99/1.49      ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6)) = iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2114]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2677,plain,
% 7.99/1.49      ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),k5_lattices(sK6))) = k5_lattices(sK6) ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2502,c_2493]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_0,plain,
% 7.99/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1,plain,
% 7.99/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_403,plain,
% 7.99/1.49      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_404,plain,
% 7.99/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_403]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_29,plain,
% 7.99/1.49      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 7.99/1.49      | r2_hidden(sK5(X0,X1,X2),X1)
% 7.99/1.49      | ~ v4_lattice3(X0)
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | ~ v10_lattices(X0) ),
% 7.99/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_500,plain,
% 7.99/1.49      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 7.99/1.49      | r2_hidden(sK5(X0,X1,X2),X1)
% 7.99/1.49      | ~ l3_lattices(X0)
% 7.99/1.49      | v2_struct_0(X0)
% 7.99/1.49      | ~ v10_lattices(X0)
% 7.99/1.49      | sK6 != X0 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_501,plain,
% 7.99/1.49      ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
% 7.99/1.49      | r2_hidden(sK5(sK6,X0,X1),X0)
% 7.99/1.49      | ~ l3_lattices(sK6)
% 7.99/1.49      | v2_struct_0(sK6)
% 7.99/1.49      | ~ v10_lattices(sK6) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_500]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_505,plain,
% 7.99/1.49      ( r2_hidden(sK5(sK6,X0,X1),X0)
% 7.99/1.49      | r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1)) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_501,c_35,c_34,c_32]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_506,plain,
% 7.99/1.49      ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
% 7.99/1.49      | r2_hidden(sK5(sK6,X0,X1),X0) ),
% 7.99/1.49      inference(renaming,[status(thm)],[c_505]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_615,plain,
% 7.99/1.49      ( r3_lattices(sK6,k15_lattice3(sK6,X0),k15_lattice3(sK6,X1))
% 7.99/1.49      | sK5(sK6,X0,X1) != X2
% 7.99/1.49      | k1_xboole_0 != X0 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_404,c_506]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_616,plain,
% 7.99/1.49      ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0)) ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_615]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2120,plain,
% 7.99/1.49      ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_59)) ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_616]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2496,plain,
% 7.99/1.49      ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_59)) = iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2120]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_3273,plain,
% 7.99/1.49      ( r3_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) = iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2677,c_2496]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2129,plain,
% 7.99/1.49      ( X0_56 != X1_56 | X2_56 != X1_56 | X2_56 = X0_56 ),
% 7.99/1.49      theory(equality) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_3241,plain,
% 7.99/1.49      ( X0_56 != X1_56
% 7.99/1.49      | k15_lattice3(sK6,X0_59) != X1_56
% 7.99/1.49      | k15_lattice3(sK6,X0_59) = X0_56 ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2129]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_3894,plain,
% 7.99/1.49      ( X0_56 != k15_lattice3(sK6,X0_59)
% 7.99/1.49      | k15_lattice3(sK6,X0_59) = X0_56
% 7.99/1.49      | k15_lattice3(sK6,X0_59) != k15_lattice3(sK6,X0_59) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_3241]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_4616,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) != k15_lattice3(sK6,X0_59)
% 7.99/1.49      | k15_lattice3(sK6,X0_59) = k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6))
% 7.99/1.49      | k15_lattice3(sK6,X0_59) != k15_lattice3(sK6,X0_59) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_3894]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_4617,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) != k15_lattice3(sK6,k1_xboole_0)
% 7.99/1.49      | k15_lattice3(sK6,k1_xboole_0) = k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6))
% 7.99/1.49      | k15_lattice3(sK6,k1_xboole_0) != k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_4616]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2674,plain,
% 7.99/1.49      ( X0_56 != X1_56
% 7.99/1.49      | k5_lattices(sK6) != X1_56
% 7.99/1.49      | k5_lattices(sK6) = X0_56 ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2129]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_3158,plain,
% 7.99/1.49      ( X0_56 != k5_lattices(sK6)
% 7.99/1.49      | k5_lattices(sK6) = X0_56
% 7.99/1.49      | k5_lattices(sK6) != k5_lattices(sK6) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2674]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_5593,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6)) != k5_lattices(sK6)
% 7.99/1.49      | k5_lattices(sK6) = k2_lattices(sK6,k15_lattice3(sK6,X0_59),k5_lattices(sK6))
% 7.99/1.49      | k5_lattices(sK6) != k5_lattices(sK6) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_3158]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_5599,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6)) != k5_lattices(sK6)
% 7.99/1.49      | k5_lattices(sK6) = k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6))
% 7.99/1.49      | k5_lattices(sK6) != k5_lattices(sK6) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_5593]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2637,plain,
% 7.99/1.49      ( k15_lattice3(sK6,k1_xboole_0) != X0_56
% 7.99/1.49      | k5_lattices(sK6) != X0_56
% 7.99/1.49      | k5_lattices(sK6) = k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2129]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_12411,plain,
% 7.99/1.49      ( k15_lattice3(sK6,k1_xboole_0) != k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6))
% 7.99/1.49      | k5_lattices(sK6) != k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k5_lattices(sK6))
% 7.99/1.49      | k5_lattices(sK6) = k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2637]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_12509,plain,
% 7.99/1.49      ( m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | k2_lattices(sK6,sK1(sK6,X0_56),sK1(sK6,k15_lattice3(sK6,X0_59))) = k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),sK1(sK6,X0_56)) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_12362,c_36,c_39,c_100,c_103,c_2138,c_2142,c_2143,
% 7.99/1.49                 c_2161,c_2871,c_2981,c_2991,c_3273,c_4617,c_5599,
% 7.99/1.49                 c_12411]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_12510,plain,
% 7.99/1.49      ( k2_lattices(sK6,sK1(sK6,X0_56),sK1(sK6,k15_lattice3(sK6,X0_59))) = k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),sK1(sK6,X0_56))
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
% 7.99/1.49      inference(renaming,[status(thm)],[c_12509]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_12515,plain,
% 7.99/1.49      ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),sK1(sK6,sK2(sK6))) = k2_lattices(sK6,sK1(sK6,sK2(sK6)),sK1(sK6,k15_lattice3(sK6,X0_59)))
% 7.99/1.49      | v13_lattices(sK6) != iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2501,c_12510]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_12670,plain,
% 7.99/1.49      ( v13_lattices(sK6) != iProver_top ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_12515,c_36,c_39,c_100,c_103,c_2138,c_2142,c_2143,
% 7.99/1.49                 c_2161,c_2871,c_2981,c_2991,c_3273,c_4617,c_5599,
% 7.99/1.49                 c_12411]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_12696,plain,
% 7.99/1.49      ( k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK1(sK6,k15_lattice3(sK6,X0_59)))) = sK1(sK6,k15_lattice3(sK6,X0_59)) ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_4639,c_12670]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2498,plain,
% 7.99/1.49      ( k2_lattices(sK6,X0_56,X1_56) = X0_56
% 7.99/1.49      | r3_lattices(sK6,X0_56,X1_56) != iProver_top
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(X1_56,u1_struct_0(sK6)) != iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2118]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_3924,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_59)) = k15_lattice3(sK6,k1_xboole_0)
% 7.99/1.49      | m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2496,c_2498]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_8125,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),k15_lattice3(sK6,X0_59)) = k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_3924,c_2159,c_2161]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_23276,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,X0_59))) = k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_12696,c_8125]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_23429,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) = k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_23276]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2996,plain,
% 7.99/1.49      ( k2_lattices(sK6,X0_56,k15_lattice3(sK6,X0_59)) = k2_lattices(sK6,k15_lattice3(sK6,X0_59),X0_56)
% 7.99/1.49      | m1_subset_1(X0_56,u1_struct_0(sK6)) != iProver_top ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2497,c_2500]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_4146,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k15_lattice3(sK6,X1_59)) = k2_lattices(sK6,k15_lattice3(sK6,X1_59),k15_lattice3(sK6,X0_59)) ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_2497,c_2996]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_8133,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_8125,c_4146]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_23240,plain,
% 7.99/1.49      ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(superposition,[status(thm)],[c_12696,c_8133]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_23400,plain,
% 7.99/1.49      ( k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) = k15_lattice3(sK6,k1_xboole_0) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_23240]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_16,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | ~ l1_lattices(X1)
% 7.99/1.49      | v13_lattices(X1)
% 7.99/1.49      | v2_struct_0(X1)
% 7.99/1.49      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 7.99/1.49      | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
% 7.99/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1083,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.99/1.49      | ~ l1_lattices(X1)
% 7.99/1.49      | v13_lattices(X1)
% 7.99/1.49      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 7.99/1.49      | k2_lattices(X1,sK1(X1,X0),X0) != X0
% 7.99/1.49      | sK6 != X1 ),
% 7.99/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1084,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | ~ l1_lattices(sK6)
% 7.99/1.49      | v13_lattices(sK6)
% 7.99/1.49      | k2_lattices(sK6,X0,sK1(sK6,X0)) != X0
% 7.99/1.49      | k2_lattices(sK6,sK1(sK6,X0),X0) != X0 ),
% 7.99/1.49      inference(unflattening,[status(thm)],[c_1083]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_1088,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.99/1.49      | v13_lattices(sK6)
% 7.99/1.49      | k2_lattices(sK6,X0,sK1(sK6,X0)) != X0
% 7.99/1.49      | k2_lattices(sK6,sK1(sK6,X0),X0) != X0 ),
% 7.99/1.49      inference(global_propositional_subsumption,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_1084,c_32,c_99]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2110,plain,
% 7.99/1.49      ( ~ m1_subset_1(X0_56,u1_struct_0(sK6))
% 7.99/1.49      | v13_lattices(sK6)
% 7.99/1.49      | k2_lattices(sK6,X0_56,sK1(sK6,X0_56)) != X0_56
% 7.99/1.49      | k2_lattices(sK6,sK1(sK6,X0_56),X0_56) != X0_56 ),
% 7.99/1.49      inference(subtyping,[status(esa)],[c_1088]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2585,plain,
% 7.99/1.49      ( ~ m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6))
% 7.99/1.49      | v13_lattices(sK6)
% 7.99/1.49      | k2_lattices(sK6,k15_lattice3(sK6,X0_59),sK1(sK6,k15_lattice3(sK6,X0_59))) != k15_lattice3(sK6,X0_59)
% 7.99/1.49      | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),k15_lattice3(sK6,X0_59)) != k15_lattice3(sK6,X0_59) ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2110]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2586,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,X0_59),sK1(sK6,k15_lattice3(sK6,X0_59))) != k15_lattice3(sK6,X0_59)
% 7.99/1.49      | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,X0_59)),k15_lattice3(sK6,X0_59)) != k15_lattice3(sK6,X0_59)
% 7.99/1.49      | m1_subset_1(k15_lattice3(sK6,X0_59),u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | v13_lattices(sK6) = iProver_top ),
% 7.99/1.49      inference(predicate_to_equality,[status(thm)],[c_2585]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(c_2588,plain,
% 7.99/1.49      ( k2_lattices(sK6,k15_lattice3(sK6,k1_xboole_0),sK1(sK6,k15_lattice3(sK6,k1_xboole_0))) != k15_lattice3(sK6,k1_xboole_0)
% 7.99/1.49      | k2_lattices(sK6,sK1(sK6,k15_lattice3(sK6,k1_xboole_0)),k15_lattice3(sK6,k1_xboole_0)) != k15_lattice3(sK6,k1_xboole_0)
% 7.99/1.49      | m1_subset_1(k15_lattice3(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 7.99/1.49      | v13_lattices(sK6) = iProver_top ),
% 7.99/1.49      inference(instantiation,[status(thm)],[c_2586]) ).
% 7.99/1.49  
% 7.99/1.49  cnf(contradiction,plain,
% 7.99/1.49      ( $false ),
% 7.99/1.49      inference(minisat,
% 7.99/1.49                [status(thm)],
% 7.99/1.49                [c_23429,c_23400,c_12670,c_2588,c_2161]) ).
% 7.99/1.49  
% 7.99/1.49  
% 7.99/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.99/1.49  
% 7.99/1.49  ------                               Statistics
% 7.99/1.49  
% 7.99/1.49  ------ General
% 7.99/1.49  
% 7.99/1.49  abstr_ref_over_cycles:                  0
% 7.99/1.49  abstr_ref_under_cycles:                 0
% 7.99/1.49  gc_basic_clause_elim:                   0
% 7.99/1.49  forced_gc_time:                         0
% 7.99/1.49  parsing_time:                           0.015
% 7.99/1.49  unif_index_cands_time:                  0.
% 7.99/1.49  unif_index_add_time:                    0.
% 7.99/1.49  orderings_time:                         0.
% 7.99/1.49  out_proof_time:                         0.017
% 7.99/1.49  total_time:                             0.908
% 7.99/1.49  num_of_symbols:                         60
% 7.99/1.49  num_of_terms:                           32130
% 7.99/1.49  
% 7.99/1.49  ------ Preprocessing
% 7.99/1.49  
% 7.99/1.49  num_of_splits:                          0
% 7.99/1.49  num_of_split_atoms:                     0
% 7.99/1.49  num_of_reused_defs:                     0
% 7.99/1.49  num_eq_ax_congr_red:                    47
% 7.99/1.49  num_of_sem_filtered_clauses:            1
% 7.99/1.49  num_of_subtypes:                        4
% 7.99/1.49  monotx_restored_types:                  0
% 7.99/1.49  sat_num_of_epr_types:                   0
% 7.99/1.49  sat_num_of_non_cyclic_types:            0
% 7.99/1.49  sat_guarded_non_collapsed_types:        1
% 7.99/1.49  num_pure_diseq_elim:                    0
% 7.99/1.49  simp_replaced_by:                       0
% 7.99/1.49  res_preprocessed:                       112
% 7.99/1.49  prep_upred:                             0
% 7.99/1.49  prep_unflattend:                        42
% 7.99/1.49  smt_new_axioms:                         0
% 7.99/1.49  pred_elim_cands:                        3
% 7.99/1.49  pred_elim:                              11
% 7.99/1.49  pred_elim_cl:                           15
% 7.99/1.49  pred_elim_cycles:                       15
% 7.99/1.49  merged_defs:                            0
% 7.99/1.49  merged_defs_ncl:                        0
% 7.99/1.49  bin_hyper_res:                          0
% 7.99/1.49  prep_cycles:                            4
% 7.99/1.49  pred_elim_time:                         0.029
% 7.99/1.49  splitting_time:                         0.
% 7.99/1.49  sem_filter_time:                        0.
% 7.99/1.49  monotx_time:                            0.
% 7.99/1.49  subtype_inf_time:                       0.
% 7.99/1.49  
% 7.99/1.49  ------ Problem properties
% 7.99/1.49  
% 7.99/1.49  clauses:                                20
% 7.99/1.49  conjectures:                            1
% 7.99/1.49  epr:                                    0
% 7.99/1.49  horn:                                   16
% 7.99/1.49  ground:                                 3
% 7.99/1.49  unary:                                  3
% 7.99/1.49  binary:                                 5
% 7.99/1.49  lits:                                   55
% 7.99/1.49  lits_eq:                                16
% 7.99/1.49  fd_pure:                                0
% 7.99/1.49  fd_pseudo:                              0
% 7.99/1.49  fd_cond:                                2
% 7.99/1.49  fd_pseudo_cond:                         0
% 7.99/1.49  ac_symbols:                             0
% 7.99/1.49  
% 7.99/1.49  ------ Propositional Solver
% 7.99/1.49  
% 7.99/1.49  prop_solver_calls:                      31
% 7.99/1.49  prop_fast_solver_calls:                 1961
% 7.99/1.49  smt_solver_calls:                       0
% 7.99/1.49  smt_fast_solver_calls:                  0
% 7.99/1.49  prop_num_of_clauses:                    13668
% 7.99/1.49  prop_preprocess_simplified:             17923
% 7.99/1.49  prop_fo_subsumed:                       132
% 7.99/1.49  prop_solver_time:                       0.
% 7.99/1.49  smt_solver_time:                        0.
% 7.99/1.49  smt_fast_solver_time:                   0.
% 7.99/1.49  prop_fast_solver_time:                  0.
% 7.99/1.49  prop_unsat_core_time:                   0.001
% 7.99/1.49  
% 7.99/1.49  ------ QBF
% 7.99/1.49  
% 7.99/1.49  qbf_q_res:                              0
% 7.99/1.49  qbf_num_tautologies:                    0
% 7.99/1.49  qbf_prep_cycles:                        0
% 7.99/1.49  
% 7.99/1.49  ------ BMC1
% 7.99/1.49  
% 7.99/1.49  bmc1_current_bound:                     -1
% 7.99/1.49  bmc1_last_solved_bound:                 -1
% 7.99/1.49  bmc1_unsat_core_size:                   -1
% 7.99/1.49  bmc1_unsat_core_parents_size:           -1
% 7.99/1.49  bmc1_merge_next_fun:                    0
% 7.99/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.99/1.49  
% 7.99/1.49  ------ Instantiation
% 7.99/1.49  
% 7.99/1.49  inst_num_of_clauses:                    2305
% 7.99/1.49  inst_num_in_passive:                    785
% 7.99/1.49  inst_num_in_active:                     837
% 7.99/1.49  inst_num_in_unprocessed:                683
% 7.99/1.49  inst_num_of_loops:                      1380
% 7.99/1.49  inst_num_of_learning_restarts:          0
% 7.99/1.49  inst_num_moves_active_passive:          541
% 7.99/1.49  inst_lit_activity:                      0
% 7.99/1.49  inst_lit_activity_moves:                1
% 7.99/1.49  inst_num_tautologies:                   0
% 7.99/1.49  inst_num_prop_implied:                  0
% 7.99/1.49  inst_num_existing_simplified:           0
% 7.99/1.49  inst_num_eq_res_simplified:             0
% 7.99/1.49  inst_num_child_elim:                    0
% 7.99/1.49  inst_num_of_dismatching_blockings:      1157
% 7.99/1.49  inst_num_of_non_proper_insts:           2339
% 7.99/1.49  inst_num_of_duplicates:                 0
% 7.99/1.49  inst_inst_num_from_inst_to_res:         0
% 7.99/1.49  inst_dismatching_checking_time:         0.
% 7.99/1.49  
% 7.99/1.49  ------ Resolution
% 7.99/1.49  
% 7.99/1.49  res_num_of_clauses:                     0
% 7.99/1.49  res_num_in_passive:                     0
% 7.99/1.49  res_num_in_active:                      0
% 7.99/1.49  res_num_of_loops:                       116
% 7.99/1.49  res_forward_subset_subsumed:            82
% 7.99/1.49  res_backward_subset_subsumed:           0
% 7.99/1.50  res_forward_subsumed:                   0
% 7.99/1.50  res_backward_subsumed:                  0
% 7.99/1.50  res_forward_subsumption_resolution:     1
% 7.99/1.50  res_backward_subsumption_resolution:    0
% 7.99/1.50  res_clause_to_clause_subsumption:       7456
% 7.99/1.50  res_orphan_elimination:                 0
% 7.99/1.50  res_tautology_del:                      159
% 7.99/1.50  res_num_eq_res_simplified:              0
% 7.99/1.50  res_num_sel_changes:                    0
% 7.99/1.50  res_moves_from_active_to_pass:          0
% 7.99/1.50  
% 7.99/1.50  ------ Superposition
% 7.99/1.50  
% 7.99/1.50  sup_time_total:                         0.
% 7.99/1.50  sup_time_generating:                    0.
% 7.99/1.50  sup_time_sim_full:                      0.
% 7.99/1.50  sup_time_sim_immed:                     0.
% 7.99/1.50  
% 7.99/1.50  sup_num_of_clauses:                     2440
% 7.99/1.50  sup_num_in_active:                      174
% 7.99/1.50  sup_num_in_passive:                     2266
% 7.99/1.50  sup_num_of_loops:                       274
% 7.99/1.50  sup_fw_superposition:                   1806
% 7.99/1.50  sup_bw_superposition:                   2062
% 7.99/1.50  sup_immediate_simplified:               586
% 7.99/1.50  sup_given_eliminated:                   0
% 7.99/1.50  comparisons_done:                       0
% 7.99/1.50  comparisons_avoided:                    105
% 7.99/1.50  
% 7.99/1.50  ------ Simplifications
% 7.99/1.50  
% 7.99/1.50  
% 7.99/1.50  sim_fw_subset_subsumed:                 37
% 7.99/1.50  sim_bw_subset_subsumed:                 431
% 7.99/1.50  sim_fw_subsumed:                        39
% 7.99/1.50  sim_bw_subsumed:                        73
% 7.99/1.50  sim_fw_subsumption_res:                 0
% 7.99/1.50  sim_bw_subsumption_res:                 0
% 7.99/1.50  sim_tautology_del:                      49
% 7.99/1.50  sim_eq_tautology_del:                   96
% 7.99/1.50  sim_eq_res_simp:                        0
% 7.99/1.50  sim_fw_demodulated:                     345
% 7.99/1.50  sim_bw_demodulated:                     1
% 7.99/1.50  sim_light_normalised:                   189
% 7.99/1.50  sim_joinable_taut:                      0
% 7.99/1.50  sim_joinable_simp:                      0
% 7.99/1.50  sim_ac_normalised:                      0
% 7.99/1.50  sim_smt_subsumption:                    0
% 7.99/1.50  
%------------------------------------------------------------------------------
