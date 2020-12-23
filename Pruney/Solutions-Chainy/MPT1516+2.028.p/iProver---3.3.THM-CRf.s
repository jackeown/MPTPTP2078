%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:21 EST 2020

% Result     : Theorem 11.48s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :  234 (34570 expanded)
%              Number of clauses        :  153 (9298 expanded)
%              Number of leaves         :   21 (6861 expanded)
%              Depth                    :   36
%              Number of atoms          : 1008 (227141 expanded)
%              Number of equality atoms :  283 (27827 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f58,plain,
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
   => ( ( k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0)
        | ~ l3_lattices(sK5)
        | ~ v13_lattices(sK5)
        | ~ v10_lattices(sK5)
        | v2_struct_0(sK5) )
      & l3_lattices(sK5)
      & v4_lattice3(sK5)
      & v10_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0)
      | ~ l3_lattices(sK5)
      | ~ v13_lattices(sK5)
      | ~ v10_lattices(sK5)
      | v2_struct_0(sK5) )
    & l3_lattices(sK5)
    & v4_lattice3(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f58])).

fof(f89,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f51,plain,(
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

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f49,f51,f50])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    v4_lattice3(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X4,X0] :
      ( k2_lattices(X0,X4,sK2(X0)) = sK2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,
    ( k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0)
    | ~ l3_lattices(sK5)
    | ~ v13_lattices(sK5)
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f9,axiom,(
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

fof(f32,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK4(X0)) != k2_lattices(X0,sK4(X0),X1)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).

fof(f80,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
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
    inference(pure_predicate_removal,[],[f2])).

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

fof(f62,plain,(
    ! [X0] :
      ( v6_lattices(X0)
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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f64,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_904,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_33])).

cnf(c_905,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
    | ~ l1_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_30,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_10,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_94,plain,
    ( l1_lattices(sK5)
    | ~ l3_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_97,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_907,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_33,c_30,c_94,c_97])).

cnf(c_2001,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_907])).

cnf(c_2303,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2001])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_976,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | v13_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_980,plain,
    ( m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v13_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_976,c_30,c_94])).

cnf(c_981,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | v13_lattices(sK5) ),
    inference(renaming,[status(thm)],[c_980])).

cnf(c_1998,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0_55),u1_struct_0(sK5))
    | v13_lattices(sK5) ),
    inference(subtyping,[status(esa)],[c_981])).

cnf(c_2306,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X0_55),u1_struct_0(sK5)) = iProver_top
    | v13_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_31,negated_conjecture,
    ( v4_lattice3(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k15_lattice3(sK5,a_2_3_lattice3(sK5,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_32,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_3_lattice3(sK5,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_33,c_32,c_30])).

cnf(c_2008,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_3_lattice3(sK5,X0_55)) = X0_55 ),
    inference(subtyping,[status(esa)],[c_467])).

cnf(c_2297,plain,
    ( k15_lattice3(sK5,a_2_3_lattice3(sK5,X0_55)) = X0_55
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2008])).

cnf(c_2821,plain,
    ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,X0_55))) = sK1(sK5,X0_55)
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
    | v13_lattices(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2306,c_2297])).

cnf(c_4233,plain,
    ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5))
    | v13_lattices(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2303,c_2821])).

cnf(c_24,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_663,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_664,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_668,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_664,c_33])).

cnf(c_2006,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_668])).

cnf(c_2299,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,X0,sK2(X1)) = sK2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_955,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | ~ v13_lattices(sK5)
    | k2_lattices(sK5,X0,sK2(sK5)) = sK2(sK5) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_959,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v13_lattices(sK5)
    | k2_lattices(sK5,X0,sK2(sK5)) = sK2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_30,c_94])).

cnf(c_1999,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ v13_lattices(sK5)
    | k2_lattices(sK5,X0_55,sK2(sK5)) = sK2(sK5) ),
    inference(subtyping,[status(esa)],[c_959])).

cnf(c_2305,plain,
    ( k2_lattices(sK5,X0_55,sK2(sK5)) = sK2(sK5)
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
    | v13_lattices(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1999])).

cnf(c_2546,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),sK2(sK5)) = sK2(sK5)
    | v13_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_2305])).

cnf(c_4277,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),sK2(sK5)) = sK2(sK5)
    | k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_4233,c_2546])).

cnf(c_29,negated_conjecture,
    ( ~ v13_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_197,negated_conjecture,
    ( ~ v13_lattices(sK5)
    | k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_33,c_32,c_30])).

cnf(c_2009,negated_conjecture,
    ( ~ v13_lattices(sK5)
    | k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_197])).

cnf(c_2025,plain,
    ( k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0)
    | v13_lattices(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2009])).

cnf(c_2013,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_2398,plain,
    ( k15_lattice3(sK5,k1_xboole_0) != X0_55
    | k5_lattices(sK5) != X0_55
    | k5_lattices(sK5) = k15_lattice3(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2013])).

cnf(c_2435,plain,
    ( k15_lattice3(sK5,k1_xboole_0) != k5_lattices(sK5)
    | k5_lattices(sK5) = k15_lattice3(sK5,k1_xboole_0)
    | k5_lattices(sK5) != k5_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_2011,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_2551,plain,
    ( k5_lattices(sK5) = k5_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_2011])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | ~ v13_lattices(sK5)
    | k2_lattices(sK5,k5_lattices(sK5),X0) = k5_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1020])).

cnf(c_1025,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v13_lattices(sK5)
    | k2_lattices(sK5,k5_lattices(sK5),X0) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1021,c_33,c_30,c_94,c_97])).

cnf(c_1996,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ v13_lattices(sK5)
    | k2_lattices(sK5,k5_lattices(sK5),X0_55) = k5_lattices(sK5) ),
    inference(subtyping,[status(esa)],[c_1025])).

cnf(c_2308,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),X0_55) = k5_lattices(sK5)
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
    | v13_lattices(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1996])).

cnf(c_2583,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5)
    | v13_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_2308])).

cnf(c_4276,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5)
    | k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_4233,c_2583])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_915,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_916,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | ~ v6_lattices(sK5)
    | k2_lattices(sK5,X0,X1) = k2_lattices(sK5,X1,X0) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_508,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_32])).

cnf(c_509,plain,
    ( v6_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_113,plain,
    ( v6_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_511,plain,
    ( v6_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_33,c_32,c_30,c_113])).

cnf(c_842,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_511])).

cnf(c_843,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X0,X1) = k2_lattices(sK5,X1,X0) ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_847,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = k2_lattices(sK5,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_843,c_33,c_30,c_94])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = k2_lattices(sK5,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_916,c_33,c_30,c_94,c_843])).

cnf(c_2003,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK5))
    | k2_lattices(sK5,X0_55,X1_55) = k2_lattices(sK5,X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_919])).

cnf(c_2301,plain,
    ( k2_lattices(sK5,X0_55,X1_55) = k2_lattices(sK5,X1_55,X0_55)
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2003])).

cnf(c_2709,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),X0_55) = k2_lattices(sK5,X0_55,k5_lattices(sK5))
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2303,c_2301])).

cnf(c_3605,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k2_lattices(sK5,k15_lattice3(sK5,X0_58),k5_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_2299,c_2709])).

cnf(c_2440,plain,
    ( k15_lattice3(sK5,a_2_3_lattice3(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_2303,c_2297])).

cnf(c_14,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_530,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_32])).

cnf(c_531,plain,
    ( ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | v9_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_119,plain,
    ( ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | v9_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_533,plain,
    ( v9_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_33,c_32,c_30,c_119])).

cnf(c_547,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_533])).

cnf(c_548,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_2,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_116,plain,
    ( v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r1_lattices(sK5,X0,X1)
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_33,c_32,c_30,c_116])).

cnf(c_553,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_552])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | ~ r1_tarski(X1,X2)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_399,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 != X3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_400,plain,
    ( r3_lattices(X0,k15_lattice3(X0,k1_xboole_0),k15_lattice3(X0,X1))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_432,plain,
    ( r3_lattices(X0,k15_lattice3(X0,k1_xboole_0),k15_lattice3(X0,X1))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_400,c_31])).

cnf(c_433,plain,
    ( r3_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_437,plain,
    ( r3_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_33,c_32,c_30])).

cnf(c_12,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_595,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_533])).

cnf(c_596,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v6_lattices(sK5)
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_600,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_33,c_32,c_30,c_113,c_116])).

cnf(c_601,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_600])).

cnf(c_690,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k15_lattice3(sK5,X2) != X1
    | k15_lattice3(sK5,k1_xboole_0) != X0
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_437,c_601])).

cnf(c_691,plain,
    ( r1_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0))
    | ~ m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_695,plain,
    ( r1_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0))
    | ~ m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_33,c_664])).

cnf(c_705,plain,
    ( r1_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_695,c_668])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = X0
    | k15_lattice3(sK5,X2) != X1
    | k15_lattice3(sK5,k1_xboole_0) != X0
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_553,c_705])).

cnf(c_733,plain,
    ( ~ m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5))
    | k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) = k15_lattice3(sK5,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( ~ m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5))
    | k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) = k15_lattice3(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_33,c_664])).

cnf(c_747,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) = k15_lattice3(sK5,k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_737,c_668])).

cnf(c_2005,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0_58)) = k15_lattice3(sK5,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_747])).

cnf(c_2894,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k5_lattices(sK5)) = k15_lattice3(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2440,c_2005])).

cnf(c_3644,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3605,c_2894])).

cnf(c_18410,plain,
    ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5))
    | k15_lattice3(sK5,k1_xboole_0) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_4276,c_3644])).

cnf(c_20035,plain,
    ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4277,c_2025,c_2435,c_2551,c_4233,c_18410])).

cnf(c_4236,plain,
    ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)))) = sK1(sK5,k15_lattice3(sK5,X0_58))
    | v13_lattices(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_2821])).

cnf(c_4336,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5)
    | k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k15_lattice3(sK5,X1_58)))) = sK1(sK5,k15_lattice3(sK5,X1_58)) ),
    inference(superposition,[status(thm)],[c_4236,c_2583])).

cnf(c_27331,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,k15_lattice3(sK5,X0_58))) = k15_lattice3(sK5,k1_xboole_0)
    | k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X1_58)) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_4336,c_2005])).

cnf(c_27620,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,sK1(sK5,k5_lattices(sK5)))) = k15_lattice3(sK5,k1_xboole_0)
    | k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_20035,c_27331])).

cnf(c_34,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( l3_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_93,plain,
    ( l1_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_95,plain,
    ( l1_lattices(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_96,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) = iProver_top
    | l1_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_98,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) = iProver_top
    | l1_lattices(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_27616,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,k15_lattice3(sK5,X0_58))) = k15_lattice3(sK5,k1_xboole_0)
    | k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_20035,c_27331])).

cnf(c_2032,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_2034,plain,
    ( m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2032])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_996,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | k2_lattices(X1,X0,sK1(X1,X0)) != X0
    | k2_lattices(X1,sK1(X1,X0),X0) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_33])).

cnf(c_997,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | v13_lattices(sK5)
    | k2_lattices(sK5,X0,sK1(sK5,X0)) != X0
    | k2_lattices(sK5,sK1(sK5,X0),X0) != X0 ),
    inference(unflattening,[status(thm)],[c_996])).

cnf(c_1001,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v13_lattices(sK5)
    | k2_lattices(sK5,X0,sK1(sK5,X0)) != X0
    | k2_lattices(sK5,sK1(sK5,X0),X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_997,c_30,c_94])).

cnf(c_1997,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | v13_lattices(sK5)
    | k2_lattices(sK5,X0_55,sK1(sK5,X0_55)) != X0_55
    | k2_lattices(sK5,sK1(sK5,X0_55),X0_55) != X0_55 ),
    inference(subtyping,[status(esa)],[c_1001])).

cnf(c_2378,plain,
    ( ~ m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5))
    | v13_lattices(sK5)
    | k2_lattices(sK5,k15_lattice3(sK5,X0_58),sK1(sK5,k15_lattice3(sK5,X0_58))) != k15_lattice3(sK5,X0_58)
    | k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)),k15_lattice3(sK5,X0_58)) != k15_lattice3(sK5,X0_58) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_2379,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),sK1(sK5,k15_lattice3(sK5,X0_58))) != k15_lattice3(sK5,X0_58)
    | k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)),k15_lattice3(sK5,X0_58)) != k15_lattice3(sK5,X0_58)
    | m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5)) != iProver_top
    | v13_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2378])).

cnf(c_2381,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,k15_lattice3(sK5,k1_xboole_0))) != k15_lattice3(sK5,k1_xboole_0)
    | k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,k1_xboole_0)),k15_lattice3(sK5,k1_xboole_0)) != k15_lattice3(sK5,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5)) != iProver_top
    | v13_lattices(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2379])).

cnf(c_20045,plain,
    ( m1_subset_1(sK1(sK5,k5_lattices(sK5)),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20035,c_2299])).

cnf(c_20188,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5)
    | v13_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_20045,c_2308])).

cnf(c_27625,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,k15_lattice3(sK5,k1_xboole_0))) = k15_lattice3(sK5,k1_xboole_0)
    | k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_27616])).

cnf(c_2710,plain,
    ( k2_lattices(sK5,X0_55,k15_lattice3(sK5,X0_58)) = k2_lattices(sK5,k15_lattice3(sK5,X0_58),X0_55)
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_2301])).

cnf(c_3824,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),k15_lattice3(sK5,X1_58)) = k2_lattices(sK5,k15_lattice3(sK5,X1_58),k15_lattice3(sK5,X0_58)) ),
    inference(superposition,[status(thm)],[c_2299,c_2710])).

cnf(c_3842,plain,
    ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3824,c_2005])).

cnf(c_27326,plain,
    ( k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0)
    | k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X1_58)) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_4336,c_3842])).

cnf(c_29179,plain,
    ( k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0)
    | k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_20035,c_27326])).

cnf(c_29191,plain,
    ( k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,k1_xboole_0)),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0)
    | k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_29179])).

cnf(c_29197,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27616,c_2034,c_2381,c_20188,c_27625,c_29191])).

cnf(c_2307,plain,
    ( k2_lattices(sK5,X0_55,sK1(sK5,X0_55)) != X0_55
    | k2_lattices(sK5,sK1(sK5,X0_55),X0_55) != X0_55
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
    | v13_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1997])).

cnf(c_29199,plain,
    ( k2_lattices(sK5,sK1(sK5,k5_lattices(sK5)),k5_lattices(sK5)) != k5_lattices(sK5)
    | m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) != iProver_top
    | v13_lattices(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_29197,c_2307])).

cnf(c_20042,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5))))) = k2_lattices(sK5,sK1(sK5,k5_lattices(sK5)),k5_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_20035,c_3605])).

cnf(c_20051,plain,
    ( k2_lattices(sK5,sK1(sK5,k5_lattices(sK5)),k5_lattices(sK5)) = k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) ),
    inference(demodulation,[status(thm)],[c_20042,c_20035])).

cnf(c_29200,plain,
    ( k5_lattices(sK5) != k5_lattices(sK5)
    | m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) != iProver_top
    | v13_lattices(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29199,c_20051,c_29197])).

cnf(c_29201,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) != iProver_top
    | v13_lattices(sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_29200])).

cnf(c_29348,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27620,c_34,c_37,c_95,c_98,c_2583,c_29201])).

cnf(c_29353,plain,
    ( k15_lattice3(sK5,k1_xboole_0) = k5_lattices(sK5) ),
    inference(demodulation,[status(thm)],[c_29348,c_3644])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29353,c_29201,c_2551,c_2435,c_2025,c_98,c_95,c_37,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:55:04 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 11.48/1.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.48/1.97  
% 11.48/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.48/1.97  
% 11.48/1.97  ------  iProver source info
% 11.48/1.97  
% 11.48/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.48/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.48/1.97  git: non_committed_changes: false
% 11.48/1.97  git: last_make_outside_of_git: false
% 11.48/1.97  
% 11.48/1.97  ------ 
% 11.48/1.97  
% 11.48/1.97  ------ Input Options
% 11.48/1.97  
% 11.48/1.97  --out_options                           all
% 11.48/1.97  --tptp_safe_out                         true
% 11.48/1.97  --problem_path                          ""
% 11.48/1.97  --include_path                          ""
% 11.48/1.97  --clausifier                            res/vclausify_rel
% 11.48/1.97  --clausifier_options                    ""
% 11.48/1.97  --stdin                                 false
% 11.48/1.97  --stats_out                             all
% 11.48/1.97  
% 11.48/1.97  ------ General Options
% 11.48/1.97  
% 11.48/1.97  --fof                                   false
% 11.48/1.97  --time_out_real                         305.
% 11.48/1.97  --time_out_virtual                      -1.
% 11.48/1.97  --symbol_type_check                     false
% 11.48/1.97  --clausify_out                          false
% 11.48/1.97  --sig_cnt_out                           false
% 11.48/1.97  --trig_cnt_out                          false
% 11.48/1.97  --trig_cnt_out_tolerance                1.
% 11.48/1.97  --trig_cnt_out_sk_spl                   false
% 11.48/1.97  --abstr_cl_out                          false
% 11.48/1.97  
% 11.48/1.97  ------ Global Options
% 11.48/1.97  
% 11.48/1.97  --schedule                              default
% 11.48/1.97  --add_important_lit                     false
% 11.48/1.97  --prop_solver_per_cl                    1000
% 11.48/1.97  --min_unsat_core                        false
% 11.48/1.97  --soft_assumptions                      false
% 11.48/1.97  --soft_lemma_size                       3
% 11.48/1.97  --prop_impl_unit_size                   0
% 11.48/1.97  --prop_impl_unit                        []
% 11.48/1.97  --share_sel_clauses                     true
% 11.48/1.97  --reset_solvers                         false
% 11.48/1.97  --bc_imp_inh                            [conj_cone]
% 11.48/1.97  --conj_cone_tolerance                   3.
% 11.48/1.97  --extra_neg_conj                        none
% 11.48/1.97  --large_theory_mode                     true
% 11.48/1.97  --prolific_symb_bound                   200
% 11.48/1.97  --lt_threshold                          2000
% 11.48/1.97  --clause_weak_htbl                      true
% 11.48/1.97  --gc_record_bc_elim                     false
% 11.48/1.97  
% 11.48/1.97  ------ Preprocessing Options
% 11.48/1.97  
% 11.48/1.97  --preprocessing_flag                    true
% 11.48/1.97  --time_out_prep_mult                    0.1
% 11.48/1.97  --splitting_mode                        input
% 11.48/1.97  --splitting_grd                         true
% 11.48/1.97  --splitting_cvd                         false
% 11.48/1.97  --splitting_cvd_svl                     false
% 11.48/1.97  --splitting_nvd                         32
% 11.48/1.97  --sub_typing                            true
% 11.48/1.97  --prep_gs_sim                           true
% 11.48/1.97  --prep_unflatten                        true
% 11.48/1.97  --prep_res_sim                          true
% 11.48/1.97  --prep_upred                            true
% 11.48/1.97  --prep_sem_filter                       exhaustive
% 11.48/1.97  --prep_sem_filter_out                   false
% 11.48/1.97  --pred_elim                             true
% 11.48/1.97  --res_sim_input                         true
% 11.48/1.97  --eq_ax_congr_red                       true
% 11.48/1.97  --pure_diseq_elim                       true
% 11.48/1.97  --brand_transform                       false
% 11.48/1.97  --non_eq_to_eq                          false
% 11.48/1.97  --prep_def_merge                        true
% 11.48/1.97  --prep_def_merge_prop_impl              false
% 11.48/1.97  --prep_def_merge_mbd                    true
% 11.48/1.97  --prep_def_merge_tr_red                 false
% 11.48/1.97  --prep_def_merge_tr_cl                  false
% 11.48/1.97  --smt_preprocessing                     true
% 11.48/1.97  --smt_ac_axioms                         fast
% 11.48/1.97  --preprocessed_out                      false
% 11.48/1.97  --preprocessed_stats                    false
% 11.48/1.97  
% 11.48/1.97  ------ Abstraction refinement Options
% 11.48/1.97  
% 11.48/1.97  --abstr_ref                             []
% 11.48/1.97  --abstr_ref_prep                        false
% 11.48/1.97  --abstr_ref_until_sat                   false
% 11.48/1.97  --abstr_ref_sig_restrict                funpre
% 11.48/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.48/1.97  --abstr_ref_under                       []
% 11.48/1.97  
% 11.48/1.97  ------ SAT Options
% 11.48/1.97  
% 11.48/1.97  --sat_mode                              false
% 11.48/1.97  --sat_fm_restart_options                ""
% 11.48/1.97  --sat_gr_def                            false
% 11.48/1.97  --sat_epr_types                         true
% 11.48/1.97  --sat_non_cyclic_types                  false
% 11.48/1.97  --sat_finite_models                     false
% 11.48/1.97  --sat_fm_lemmas                         false
% 11.48/1.97  --sat_fm_prep                           false
% 11.48/1.97  --sat_fm_uc_incr                        true
% 11.48/1.97  --sat_out_model                         small
% 11.48/1.97  --sat_out_clauses                       false
% 11.48/1.97  
% 11.48/1.97  ------ QBF Options
% 11.48/1.97  
% 11.48/1.97  --qbf_mode                              false
% 11.48/1.97  --qbf_elim_univ                         false
% 11.48/1.97  --qbf_dom_inst                          none
% 11.48/1.97  --qbf_dom_pre_inst                      false
% 11.48/1.97  --qbf_sk_in                             false
% 11.48/1.97  --qbf_pred_elim                         true
% 11.48/1.97  --qbf_split                             512
% 11.48/1.97  
% 11.48/1.97  ------ BMC1 Options
% 11.48/1.97  
% 11.48/1.97  --bmc1_incremental                      false
% 11.48/1.97  --bmc1_axioms                           reachable_all
% 11.48/1.97  --bmc1_min_bound                        0
% 11.48/1.97  --bmc1_max_bound                        -1
% 11.48/1.97  --bmc1_max_bound_default                -1
% 11.48/1.97  --bmc1_symbol_reachability              true
% 11.48/1.97  --bmc1_property_lemmas                  false
% 11.48/1.97  --bmc1_k_induction                      false
% 11.48/1.97  --bmc1_non_equiv_states                 false
% 11.48/1.97  --bmc1_deadlock                         false
% 11.48/1.97  --bmc1_ucm                              false
% 11.48/1.97  --bmc1_add_unsat_core                   none
% 11.48/1.97  --bmc1_unsat_core_children              false
% 11.48/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.48/1.97  --bmc1_out_stat                         full
% 11.48/1.97  --bmc1_ground_init                      false
% 11.48/1.97  --bmc1_pre_inst_next_state              false
% 11.48/1.97  --bmc1_pre_inst_state                   false
% 11.48/1.97  --bmc1_pre_inst_reach_state             false
% 11.48/1.97  --bmc1_out_unsat_core                   false
% 11.48/1.97  --bmc1_aig_witness_out                  false
% 11.48/1.97  --bmc1_verbose                          false
% 11.48/1.97  --bmc1_dump_clauses_tptp                false
% 11.48/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.48/1.97  --bmc1_dump_file                        -
% 11.48/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.48/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.48/1.97  --bmc1_ucm_extend_mode                  1
% 11.48/1.97  --bmc1_ucm_init_mode                    2
% 11.48/1.97  --bmc1_ucm_cone_mode                    none
% 11.48/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.48/1.97  --bmc1_ucm_relax_model                  4
% 11.48/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.48/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.48/1.97  --bmc1_ucm_layered_model                none
% 11.48/1.97  --bmc1_ucm_max_lemma_size               10
% 11.48/1.97  
% 11.48/1.97  ------ AIG Options
% 11.48/1.97  
% 11.48/1.97  --aig_mode                              false
% 11.48/1.97  
% 11.48/1.97  ------ Instantiation Options
% 11.48/1.97  
% 11.48/1.97  --instantiation_flag                    true
% 11.48/1.97  --inst_sos_flag                         true
% 11.48/1.97  --inst_sos_phase                        true
% 11.48/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.48/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.48/1.97  --inst_lit_sel_side                     num_symb
% 11.48/1.97  --inst_solver_per_active                1400
% 11.48/1.97  --inst_solver_calls_frac                1.
% 11.48/1.97  --inst_passive_queue_type               priority_queues
% 11.48/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.48/1.97  --inst_passive_queues_freq              [25;2]
% 11.48/1.97  --inst_dismatching                      true
% 11.48/1.97  --inst_eager_unprocessed_to_passive     true
% 11.48/1.97  --inst_prop_sim_given                   true
% 11.48/1.97  --inst_prop_sim_new                     false
% 11.48/1.97  --inst_subs_new                         false
% 11.48/1.97  --inst_eq_res_simp                      false
% 11.48/1.97  --inst_subs_given                       false
% 11.48/1.97  --inst_orphan_elimination               true
% 11.48/1.97  --inst_learning_loop_flag               true
% 11.48/1.97  --inst_learning_start                   3000
% 11.48/1.97  --inst_learning_factor                  2
% 11.48/1.97  --inst_start_prop_sim_after_learn       3
% 11.48/1.97  --inst_sel_renew                        solver
% 11.48/1.97  --inst_lit_activity_flag                true
% 11.48/1.97  --inst_restr_to_given                   false
% 11.48/1.97  --inst_activity_threshold               500
% 11.48/1.97  --inst_out_proof                        true
% 11.48/1.97  
% 11.48/1.97  ------ Resolution Options
% 11.48/1.97  
% 11.48/1.97  --resolution_flag                       true
% 11.48/1.97  --res_lit_sel                           adaptive
% 11.48/1.97  --res_lit_sel_side                      none
% 11.48/1.97  --res_ordering                          kbo
% 11.48/1.97  --res_to_prop_solver                    active
% 11.48/1.97  --res_prop_simpl_new                    false
% 11.48/1.97  --res_prop_simpl_given                  true
% 11.48/1.97  --res_passive_queue_type                priority_queues
% 11.48/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.48/1.97  --res_passive_queues_freq               [15;5]
% 11.48/1.97  --res_forward_subs                      full
% 11.48/1.97  --res_backward_subs                     full
% 11.48/1.97  --res_forward_subs_resolution           true
% 11.48/1.97  --res_backward_subs_resolution          true
% 11.48/1.97  --res_orphan_elimination                true
% 11.48/1.97  --res_time_limit                        2.
% 11.48/1.97  --res_out_proof                         true
% 11.48/1.97  
% 11.48/1.97  ------ Superposition Options
% 11.48/1.97  
% 11.48/1.97  --superposition_flag                    true
% 11.48/1.97  --sup_passive_queue_type                priority_queues
% 11.48/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.48/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.48/1.97  --demod_completeness_check              fast
% 11.48/1.97  --demod_use_ground                      true
% 11.48/1.97  --sup_to_prop_solver                    passive
% 11.48/1.97  --sup_prop_simpl_new                    true
% 11.48/1.97  --sup_prop_simpl_given                  true
% 11.48/1.97  --sup_fun_splitting                     true
% 11.48/1.97  --sup_smt_interval                      50000
% 11.48/1.97  
% 11.48/1.97  ------ Superposition Simplification Setup
% 11.48/1.97  
% 11.48/1.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.48/1.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.48/1.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.48/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.48/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.48/1.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.48/1.97  --sup_immed_triv                        [TrivRules]
% 11.48/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.97  --sup_immed_bw_main                     []
% 11.48/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.48/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.48/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.97  --sup_input_bw                          []
% 11.48/1.97  
% 11.48/1.97  ------ Combination Options
% 11.48/1.97  
% 11.48/1.97  --comb_res_mult                         3
% 11.48/1.97  --comb_sup_mult                         2
% 11.48/1.97  --comb_inst_mult                        10
% 11.48/1.97  
% 11.48/1.97  ------ Debug Options
% 11.48/1.97  
% 11.48/1.97  --dbg_backtrace                         false
% 11.48/1.97  --dbg_dump_prop_clauses                 false
% 11.48/1.97  --dbg_dump_prop_clauses_file            -
% 11.48/1.97  --dbg_out_stat                          false
% 11.48/1.97  ------ Parsing...
% 11.48/1.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.48/1.97  
% 11.48/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 11.48/1.97  
% 11.48/1.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.48/1.97  
% 11.48/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.48/1.97  ------ Proving...
% 11.48/1.97  ------ Problem Properties 
% 11.48/1.97  
% 11.48/1.97  
% 11.48/1.97  clauses                                 17
% 11.48/1.97  conjectures                             1
% 11.48/1.97  EPR                                     0
% 11.48/1.97  Horn                                    15
% 11.48/1.97  unary                                   3
% 11.48/1.97  binary                                  4
% 11.48/1.97  lits                                    45
% 11.48/1.97  lits eq                                 16
% 11.48/1.97  fd_pure                                 0
% 11.48/1.97  fd_pseudo                               0
% 11.48/1.97  fd_cond                                 2
% 11.48/1.97  fd_pseudo_cond                          0
% 11.48/1.97  AC symbols                              0
% 11.48/1.97  
% 11.48/1.97  ------ Schedule dynamic 5 is on 
% 11.48/1.97  
% 11.48/1.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.48/1.97  
% 11.48/1.97  
% 11.48/1.97  ------ 
% 11.48/1.97  Current options:
% 11.48/1.97  ------ 
% 11.48/1.97  
% 11.48/1.97  ------ Input Options
% 11.48/1.97  
% 11.48/1.97  --out_options                           all
% 11.48/1.97  --tptp_safe_out                         true
% 11.48/1.97  --problem_path                          ""
% 11.48/1.97  --include_path                          ""
% 11.48/1.97  --clausifier                            res/vclausify_rel
% 11.48/1.97  --clausifier_options                    ""
% 11.48/1.97  --stdin                                 false
% 11.48/1.97  --stats_out                             all
% 11.48/1.97  
% 11.48/1.97  ------ General Options
% 11.48/1.97  
% 11.48/1.97  --fof                                   false
% 11.48/1.97  --time_out_real                         305.
% 11.48/1.97  --time_out_virtual                      -1.
% 11.48/1.97  --symbol_type_check                     false
% 11.48/1.97  --clausify_out                          false
% 11.48/1.97  --sig_cnt_out                           false
% 11.48/1.97  --trig_cnt_out                          false
% 11.48/1.97  --trig_cnt_out_tolerance                1.
% 11.48/1.97  --trig_cnt_out_sk_spl                   false
% 11.48/1.97  --abstr_cl_out                          false
% 11.48/1.97  
% 11.48/1.97  ------ Global Options
% 11.48/1.97  
% 11.48/1.97  --schedule                              default
% 11.48/1.97  --add_important_lit                     false
% 11.48/1.97  --prop_solver_per_cl                    1000
% 11.48/1.97  --min_unsat_core                        false
% 11.48/1.97  --soft_assumptions                      false
% 11.48/1.97  --soft_lemma_size                       3
% 11.48/1.97  --prop_impl_unit_size                   0
% 11.48/1.97  --prop_impl_unit                        []
% 11.48/1.97  --share_sel_clauses                     true
% 11.48/1.97  --reset_solvers                         false
% 11.48/1.97  --bc_imp_inh                            [conj_cone]
% 11.48/1.97  --conj_cone_tolerance                   3.
% 11.48/1.97  --extra_neg_conj                        none
% 11.48/1.97  --large_theory_mode                     true
% 11.48/1.97  --prolific_symb_bound                   200
% 11.48/1.97  --lt_threshold                          2000
% 11.48/1.97  --clause_weak_htbl                      true
% 11.48/1.97  --gc_record_bc_elim                     false
% 11.48/1.97  
% 11.48/1.97  ------ Preprocessing Options
% 11.48/1.97  
% 11.48/1.97  --preprocessing_flag                    true
% 11.48/1.97  --time_out_prep_mult                    0.1
% 11.48/1.97  --splitting_mode                        input
% 11.48/1.97  --splitting_grd                         true
% 11.48/1.97  --splitting_cvd                         false
% 11.48/1.97  --splitting_cvd_svl                     false
% 11.48/1.97  --splitting_nvd                         32
% 11.48/1.97  --sub_typing                            true
% 11.48/1.97  --prep_gs_sim                           true
% 11.48/1.97  --prep_unflatten                        true
% 11.48/1.97  --prep_res_sim                          true
% 11.48/1.97  --prep_upred                            true
% 11.48/1.97  --prep_sem_filter                       exhaustive
% 11.48/1.97  --prep_sem_filter_out                   false
% 11.48/1.97  --pred_elim                             true
% 11.48/1.97  --res_sim_input                         true
% 11.48/1.97  --eq_ax_congr_red                       true
% 11.48/1.97  --pure_diseq_elim                       true
% 11.48/1.97  --brand_transform                       false
% 11.48/1.97  --non_eq_to_eq                          false
% 11.48/1.97  --prep_def_merge                        true
% 11.48/1.97  --prep_def_merge_prop_impl              false
% 11.48/1.97  --prep_def_merge_mbd                    true
% 11.48/1.97  --prep_def_merge_tr_red                 false
% 11.48/1.97  --prep_def_merge_tr_cl                  false
% 11.48/1.97  --smt_preprocessing                     true
% 11.48/1.97  --smt_ac_axioms                         fast
% 11.48/1.97  --preprocessed_out                      false
% 11.48/1.97  --preprocessed_stats                    false
% 11.48/1.97  
% 11.48/1.97  ------ Abstraction refinement Options
% 11.48/1.97  
% 11.48/1.97  --abstr_ref                             []
% 11.48/1.97  --abstr_ref_prep                        false
% 11.48/1.97  --abstr_ref_until_sat                   false
% 11.48/1.97  --abstr_ref_sig_restrict                funpre
% 11.48/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.48/1.97  --abstr_ref_under                       []
% 11.48/1.97  
% 11.48/1.97  ------ SAT Options
% 11.48/1.97  
% 11.48/1.97  --sat_mode                              false
% 11.48/1.97  --sat_fm_restart_options                ""
% 11.48/1.97  --sat_gr_def                            false
% 11.48/1.97  --sat_epr_types                         true
% 11.48/1.97  --sat_non_cyclic_types                  false
% 11.48/1.97  --sat_finite_models                     false
% 11.48/1.97  --sat_fm_lemmas                         false
% 11.48/1.97  --sat_fm_prep                           false
% 11.48/1.97  --sat_fm_uc_incr                        true
% 11.48/1.97  --sat_out_model                         small
% 11.48/1.97  --sat_out_clauses                       false
% 11.48/1.97  
% 11.48/1.97  ------ QBF Options
% 11.48/1.97  
% 11.48/1.97  --qbf_mode                              false
% 11.48/1.97  --qbf_elim_univ                         false
% 11.48/1.97  --qbf_dom_inst                          none
% 11.48/1.97  --qbf_dom_pre_inst                      false
% 11.48/1.97  --qbf_sk_in                             false
% 11.48/1.97  --qbf_pred_elim                         true
% 11.48/1.97  --qbf_split                             512
% 11.48/1.97  
% 11.48/1.97  ------ BMC1 Options
% 11.48/1.97  
% 11.48/1.97  --bmc1_incremental                      false
% 11.48/1.97  --bmc1_axioms                           reachable_all
% 11.48/1.97  --bmc1_min_bound                        0
% 11.48/1.97  --bmc1_max_bound                        -1
% 11.48/1.97  --bmc1_max_bound_default                -1
% 11.48/1.97  --bmc1_symbol_reachability              true
% 11.48/1.97  --bmc1_property_lemmas                  false
% 11.48/1.97  --bmc1_k_induction                      false
% 11.48/1.97  --bmc1_non_equiv_states                 false
% 11.48/1.97  --bmc1_deadlock                         false
% 11.48/1.97  --bmc1_ucm                              false
% 11.48/1.97  --bmc1_add_unsat_core                   none
% 11.48/1.97  --bmc1_unsat_core_children              false
% 11.48/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.48/1.97  --bmc1_out_stat                         full
% 11.48/1.97  --bmc1_ground_init                      false
% 11.48/1.97  --bmc1_pre_inst_next_state              false
% 11.48/1.97  --bmc1_pre_inst_state                   false
% 11.48/1.97  --bmc1_pre_inst_reach_state             false
% 11.48/1.97  --bmc1_out_unsat_core                   false
% 11.48/1.97  --bmc1_aig_witness_out                  false
% 11.48/1.97  --bmc1_verbose                          false
% 11.48/1.97  --bmc1_dump_clauses_tptp                false
% 11.48/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.48/1.97  --bmc1_dump_file                        -
% 11.48/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.48/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.48/1.97  --bmc1_ucm_extend_mode                  1
% 11.48/1.97  --bmc1_ucm_init_mode                    2
% 11.48/1.97  --bmc1_ucm_cone_mode                    none
% 11.48/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.48/1.97  --bmc1_ucm_relax_model                  4
% 11.48/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.48/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.48/1.97  --bmc1_ucm_layered_model                none
% 11.48/1.97  --bmc1_ucm_max_lemma_size               10
% 11.48/1.97  
% 11.48/1.97  ------ AIG Options
% 11.48/1.97  
% 11.48/1.97  --aig_mode                              false
% 11.48/1.97  
% 11.48/1.97  ------ Instantiation Options
% 11.48/1.97  
% 11.48/1.97  --instantiation_flag                    true
% 11.48/1.97  --inst_sos_flag                         true
% 11.48/1.97  --inst_sos_phase                        true
% 11.48/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.48/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.48/1.97  --inst_lit_sel_side                     none
% 11.48/1.97  --inst_solver_per_active                1400
% 11.48/1.97  --inst_solver_calls_frac                1.
% 11.48/1.97  --inst_passive_queue_type               priority_queues
% 11.48/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.48/1.97  --inst_passive_queues_freq              [25;2]
% 11.48/1.97  --inst_dismatching                      true
% 11.48/1.97  --inst_eager_unprocessed_to_passive     true
% 11.48/1.97  --inst_prop_sim_given                   true
% 11.48/1.97  --inst_prop_sim_new                     false
% 11.48/1.97  --inst_subs_new                         false
% 11.48/1.97  --inst_eq_res_simp                      false
% 11.48/1.97  --inst_subs_given                       false
% 11.48/1.97  --inst_orphan_elimination               true
% 11.48/1.97  --inst_learning_loop_flag               true
% 11.48/1.97  --inst_learning_start                   3000
% 11.48/1.97  --inst_learning_factor                  2
% 11.48/1.97  --inst_start_prop_sim_after_learn       3
% 11.48/1.97  --inst_sel_renew                        solver
% 11.48/1.97  --inst_lit_activity_flag                true
% 11.48/1.97  --inst_restr_to_given                   false
% 11.48/1.97  --inst_activity_threshold               500
% 11.48/1.97  --inst_out_proof                        true
% 11.48/1.97  
% 11.48/1.97  ------ Resolution Options
% 11.48/1.97  
% 11.48/1.97  --resolution_flag                       false
% 11.48/1.97  --res_lit_sel                           adaptive
% 11.48/1.97  --res_lit_sel_side                      none
% 11.48/1.97  --res_ordering                          kbo
% 11.48/1.97  --res_to_prop_solver                    active
% 11.48/1.97  --res_prop_simpl_new                    false
% 11.48/1.97  --res_prop_simpl_given                  true
% 11.48/1.97  --res_passive_queue_type                priority_queues
% 11.48/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.48/1.97  --res_passive_queues_freq               [15;5]
% 11.48/1.97  --res_forward_subs                      full
% 11.48/1.97  --res_backward_subs                     full
% 11.48/1.97  --res_forward_subs_resolution           true
% 11.48/1.97  --res_backward_subs_resolution          true
% 11.48/1.97  --res_orphan_elimination                true
% 11.48/1.97  --res_time_limit                        2.
% 11.48/1.97  --res_out_proof                         true
% 11.48/1.97  
% 11.48/1.97  ------ Superposition Options
% 11.48/1.97  
% 11.48/1.97  --superposition_flag                    true
% 11.48/1.97  --sup_passive_queue_type                priority_queues
% 11.48/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.48/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.48/1.97  --demod_completeness_check              fast
% 11.48/1.97  --demod_use_ground                      true
% 11.48/1.97  --sup_to_prop_solver                    passive
% 11.48/1.97  --sup_prop_simpl_new                    true
% 11.48/1.97  --sup_prop_simpl_given                  true
% 11.48/1.97  --sup_fun_splitting                     true
% 11.48/1.97  --sup_smt_interval                      50000
% 11.48/1.97  
% 11.48/1.97  ------ Superposition Simplification Setup
% 11.48/1.97  
% 11.48/1.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.48/1.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.48/1.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.48/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.48/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.48/1.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.48/1.97  --sup_immed_triv                        [TrivRules]
% 11.48/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.97  --sup_immed_bw_main                     []
% 11.48/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.48/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.48/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.97  --sup_input_bw                          []
% 11.48/1.97  
% 11.48/1.97  ------ Combination Options
% 11.48/1.97  
% 11.48/1.97  --comb_res_mult                         3
% 11.48/1.97  --comb_sup_mult                         2
% 11.48/1.97  --comb_inst_mult                        10
% 11.48/1.97  
% 11.48/1.97  ------ Debug Options
% 11.48/1.97  
% 11.48/1.97  --dbg_backtrace                         false
% 11.48/1.97  --dbg_dump_prop_clauses                 false
% 11.48/1.97  --dbg_dump_prop_clauses_file            -
% 11.48/1.97  --dbg_out_stat                          false
% 11.48/1.97  
% 11.48/1.97  
% 11.48/1.97  
% 11.48/1.97  
% 11.48/1.97  ------ Proving...
% 11.48/1.97  
% 11.48/1.97  
% 11.48/1.97  % SZS status Theorem for theBenchmark.p
% 11.48/1.97  
% 11.48/1.97  % SZS output start CNFRefutation for theBenchmark.p
% 11.48/1.97  
% 11.48/1.97  fof(f4,axiom,(
% 11.48/1.97    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 11.48/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.97  
% 11.48/1.97  fof(f23,plain,(
% 11.48/1.97    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.48/1.97    inference(ennf_transformation,[],[f4])).
% 11.48/1.97  
% 11.48/1.97  fof(f24,plain,(
% 11.48/1.97    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(flattening,[],[f23])).
% 11.48/1.97  
% 11.48/1.97  fof(f69,plain,(
% 11.48/1.97    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.97    inference(cnf_transformation,[],[f24])).
% 11.48/1.97  
% 11.48/1.97  fof(f13,conjecture,(
% 11.48/1.97    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.48/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.97  
% 11.48/1.97  fof(f14,negated_conjecture,(
% 11.48/1.97    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.48/1.97    inference(negated_conjecture,[],[f13])).
% 11.48/1.97  
% 11.48/1.97  fof(f40,plain,(
% 11.48/1.97    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.48/1.97    inference(ennf_transformation,[],[f14])).
% 11.48/1.97  
% 11.48/1.97  fof(f41,plain,(
% 11.48/1.97    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 11.48/1.97    inference(flattening,[],[f40])).
% 11.48/1.97  
% 11.48/1.97  fof(f58,plain,(
% 11.48/1.97    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0) | ~l3_lattices(sK5) | ~v13_lattices(sK5) | ~v10_lattices(sK5) | v2_struct_0(sK5)) & l3_lattices(sK5) & v4_lattice3(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5))),
% 11.48/1.97    introduced(choice_axiom,[])).
% 11.48/1.97  
% 11.48/1.97  fof(f59,plain,(
% 11.48/1.97    (k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0) | ~l3_lattices(sK5) | ~v13_lattices(sK5) | ~v10_lattices(sK5) | v2_struct_0(sK5)) & l3_lattices(sK5) & v4_lattice3(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5)),
% 11.48/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f58])).
% 11.48/1.97  
% 11.48/1.97  fof(f89,plain,(
% 11.48/1.97    ~v2_struct_0(sK5)),
% 11.48/1.97    inference(cnf_transformation,[],[f59])).
% 11.48/1.97  
% 11.48/1.97  fof(f92,plain,(
% 11.48/1.97    l3_lattices(sK5)),
% 11.48/1.97    inference(cnf_transformation,[],[f59])).
% 11.48/1.97  
% 11.48/1.97  fof(f5,axiom,(
% 11.48/1.97    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 11.48/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.97  
% 11.48/1.97  fof(f15,plain,(
% 11.48/1.97    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 11.48/1.97    inference(pure_predicate_removal,[],[f5])).
% 11.48/1.97  
% 11.48/1.97  fof(f25,plain,(
% 11.48/1.97    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 11.48/1.97    inference(ennf_transformation,[],[f15])).
% 11.48/1.97  
% 11.48/1.97  fof(f70,plain,(
% 11.48/1.97    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 11.48/1.97    inference(cnf_transformation,[],[f25])).
% 11.48/1.97  
% 11.48/1.97  fof(f8,axiom,(
% 11.48/1.97    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 11.48/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.97  
% 11.48/1.97  fof(f30,plain,(
% 11.48/1.97    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.48/1.97    inference(ennf_transformation,[],[f8])).
% 11.48/1.97  
% 11.48/1.97  fof(f31,plain,(
% 11.48/1.97    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(flattening,[],[f30])).
% 11.48/1.97  
% 11.48/1.97  fof(f48,plain,(
% 11.48/1.97    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(nnf_transformation,[],[f31])).
% 11.48/1.97  
% 11.48/1.97  fof(f49,plain,(
% 11.48/1.97    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(rectify,[],[f48])).
% 11.48/1.97  
% 11.48/1.97  fof(f51,plain,(
% 11.48/1.97    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 11.48/1.97    introduced(choice_axiom,[])).
% 11.48/1.97  
% 11.48/1.97  fof(f50,plain,(
% 11.48/1.97    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 11.48/1.97    introduced(choice_axiom,[])).
% 11.48/1.97  
% 11.48/1.97  fof(f52,plain,(
% 11.48/1.97    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((k2_lattices(X0,X4,sK2(X0)) = sK2(X0) & k2_lattices(X0,sK2(X0),X4) = sK2(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f49,f51,f50])).
% 11.48/1.97  
% 11.48/1.97  fof(f78,plain,(
% 11.48/1.97    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.97    inference(cnf_transformation,[],[f52])).
% 11.48/1.97  
% 11.48/1.97  fof(f11,axiom,(
% 11.48/1.97    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 11.48/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.97  
% 11.48/1.97  fof(f36,plain,(
% 11.48/1.97    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.48/1.97    inference(ennf_transformation,[],[f11])).
% 11.48/1.97  
% 11.48/1.97  fof(f37,plain,(
% 11.48/1.97    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(flattening,[],[f36])).
% 11.48/1.97  
% 11.48/1.97  fof(f85,plain,(
% 11.48/1.97    ( ! [X0,X1] : (k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.97    inference(cnf_transformation,[],[f37])).
% 11.48/1.97  
% 11.48/1.97  fof(f91,plain,(
% 11.48/1.97    v4_lattice3(sK5)),
% 11.48/1.97    inference(cnf_transformation,[],[f59])).
% 11.48/1.97  
% 11.48/1.97  fof(f90,plain,(
% 11.48/1.97    v10_lattices(sK5)),
% 11.48/1.97    inference(cnf_transformation,[],[f59])).
% 11.48/1.97  
% 11.48/1.97  fof(f10,axiom,(
% 11.48/1.97    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 11.48/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.97  
% 11.48/1.97  fof(f34,plain,(
% 11.48/1.97    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.48/1.97    inference(ennf_transformation,[],[f10])).
% 11.48/1.97  
% 11.48/1.97  fof(f35,plain,(
% 11.48/1.97    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(flattening,[],[f34])).
% 11.48/1.97  
% 11.48/1.97  fof(f84,plain,(
% 11.48/1.97    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.97    inference(cnf_transformation,[],[f35])).
% 11.48/1.97  
% 11.48/1.97  fof(f77,plain,(
% 11.48/1.97    ( ! [X4,X0] : (k2_lattices(X0,X4,sK2(X0)) = sK2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.97    inference(cnf_transformation,[],[f52])).
% 11.48/1.97  
% 11.48/1.97  fof(f93,plain,(
% 11.48/1.97    k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0) | ~l3_lattices(sK5) | ~v13_lattices(sK5) | ~v10_lattices(sK5) | v2_struct_0(sK5)),
% 11.48/1.97    inference(cnf_transformation,[],[f59])).
% 11.48/1.97  
% 11.48/1.97  fof(f3,axiom,(
% 11.48/1.97    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 11.48/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.97  
% 11.48/1.97  fof(f21,plain,(
% 11.48/1.97    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.48/1.97    inference(ennf_transformation,[],[f3])).
% 11.48/1.97  
% 11.48/1.97  fof(f22,plain,(
% 11.48/1.97    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(flattening,[],[f21])).
% 11.48/1.97  
% 11.48/1.97  fof(f42,plain,(
% 11.48/1.97    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(nnf_transformation,[],[f22])).
% 11.48/1.97  
% 11.48/1.97  fof(f43,plain,(
% 11.48/1.97    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(rectify,[],[f42])).
% 11.48/1.97  
% 11.48/1.97  fof(f44,plain,(
% 11.48/1.97    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 11.48/1.97    introduced(choice_axiom,[])).
% 11.48/1.97  
% 11.48/1.97  fof(f45,plain,(
% 11.48/1.97    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 11.48/1.97  
% 11.48/1.97  fof(f65,plain,(
% 11.48/1.97    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.97    inference(cnf_transformation,[],[f45])).
% 11.48/1.97  
% 11.48/1.97  fof(f95,plain,(
% 11.48/1.97    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.97    inference(equality_resolution,[],[f65])).
% 11.48/1.97  
% 11.48/1.97  fof(f9,axiom,(
% 11.48/1.97    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 11.48/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.97  
% 11.48/1.97  fof(f32,plain,(
% 11.48/1.97    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.48/1.97    inference(ennf_transformation,[],[f9])).
% 11.48/1.97  
% 11.48/1.97  fof(f33,plain,(
% 11.48/1.98    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.98    inference(flattening,[],[f32])).
% 11.48/1.98  
% 11.48/1.98  fof(f53,plain,(
% 11.48/1.98    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.98    inference(nnf_transformation,[],[f33])).
% 11.48/1.98  
% 11.48/1.98  fof(f54,plain,(
% 11.48/1.98    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.98    inference(rectify,[],[f53])).
% 11.48/1.98  
% 11.48/1.98  fof(f56,plain,(
% 11.48/1.98    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK4(X0)) != k2_lattices(X0,sK4(X0),X1) & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 11.48/1.98    introduced(choice_axiom,[])).
% 11.48/1.98  
% 11.48/1.98  fof(f55,plain,(
% 11.48/1.98    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK3(X0)) != k2_lattices(X0,sK3(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 11.48/1.98    introduced(choice_axiom,[])).
% 11.48/1.98  
% 11.48/1.98  fof(f57,plain,(
% 11.48/1.98    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK3(X0),sK4(X0)) != k2_lattices(X0,sK4(X0),sK3(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).
% 11.48/1.98  
% 11.48/1.98  fof(f80,plain,(
% 11.48/1.98    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f57])).
% 11.48/1.98  
% 11.48/1.98  fof(f2,axiom,(
% 11.48/1.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.48/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f16,plain,(
% 11.48/1.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.48/1.98    inference(pure_predicate_removal,[],[f2])).
% 11.48/1.98  
% 11.48/1.98  fof(f17,plain,(
% 11.48/1.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.48/1.98    inference(pure_predicate_removal,[],[f16])).
% 11.48/1.98  
% 11.48/1.98  fof(f18,plain,(
% 11.48/1.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 11.48/1.98    inference(pure_predicate_removal,[],[f17])).
% 11.48/1.98  
% 11.48/1.98  fof(f19,plain,(
% 11.48/1.98    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 11.48/1.98    inference(ennf_transformation,[],[f18])).
% 11.48/1.98  
% 11.48/1.98  fof(f20,plain,(
% 11.48/1.98    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 11.48/1.98    inference(flattening,[],[f19])).
% 11.48/1.98  
% 11.48/1.98  fof(f62,plain,(
% 11.48/1.98    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f20])).
% 11.48/1.98  
% 11.48/1.98  fof(f7,axiom,(
% 11.48/1.98    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 11.48/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f28,plain,(
% 11.48/1.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 11.48/1.98    inference(ennf_transformation,[],[f7])).
% 11.48/1.98  
% 11.48/1.98  fof(f29,plain,(
% 11.48/1.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.98    inference(flattening,[],[f28])).
% 11.48/1.98  
% 11.48/1.98  fof(f47,plain,(
% 11.48/1.98    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.98    inference(nnf_transformation,[],[f29])).
% 11.48/1.98  
% 11.48/1.98  fof(f73,plain,(
% 11.48/1.98    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f47])).
% 11.48/1.98  
% 11.48/1.98  fof(f64,plain,(
% 11.48/1.98    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f20])).
% 11.48/1.98  
% 11.48/1.98  fof(f63,plain,(
% 11.48/1.98    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f20])).
% 11.48/1.98  
% 11.48/1.98  fof(f1,axiom,(
% 11.48/1.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.48/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f60,plain,(
% 11.48/1.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f1])).
% 11.48/1.98  
% 11.48/1.98  fof(f12,axiom,(
% 11.48/1.98    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 11.48/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f38,plain,(
% 11.48/1.98    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.48/1.98    inference(ennf_transformation,[],[f12])).
% 11.48/1.98  
% 11.48/1.98  fof(f39,plain,(
% 11.48/1.98    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.98    inference(flattening,[],[f38])).
% 11.48/1.98  
% 11.48/1.98  fof(f87,plain,(
% 11.48/1.98    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~r1_tarski(X1,X2) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f39])).
% 11.48/1.98  
% 11.48/1.98  fof(f6,axiom,(
% 11.48/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 11.48/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f26,plain,(
% 11.48/1.98    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 11.48/1.98    inference(ennf_transformation,[],[f6])).
% 11.48/1.98  
% 11.48/1.98  fof(f27,plain,(
% 11.48/1.98    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.98    inference(flattening,[],[f26])).
% 11.48/1.98  
% 11.48/1.98  fof(f46,plain,(
% 11.48/1.98    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 11.48/1.98    inference(nnf_transformation,[],[f27])).
% 11.48/1.98  
% 11.48/1.98  fof(f71,plain,(
% 11.48/1.98    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f46])).
% 11.48/1.98  
% 11.48/1.98  fof(f79,plain,(
% 11.48/1.98    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f52])).
% 11.48/1.98  
% 11.48/1.98  cnf(c_9,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 11.48/1.98      | ~ l1_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f69]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_33,negated_conjecture,
% 11.48/1.98      ( ~ v2_struct_0(sK5) ),
% 11.48/1.98      inference(cnf_transformation,[],[f89]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_904,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 11.48/1.98      | ~ l1_lattices(X0)
% 11.48/1.98      | sK5 != X0 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_9,c_33]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_905,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
% 11.48/1.98      | ~ l1_lattices(sK5) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_904]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_30,negated_conjecture,
% 11.48/1.98      ( l3_lattices(sK5) ),
% 11.48/1.98      inference(cnf_transformation,[],[f92]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_10,plain,
% 11.48/1.98      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f70]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_94,plain,
% 11.48/1.98      ( l1_lattices(sK5) | ~ l3_lattices(sK5) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_10]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_97,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
% 11.48/1.98      | ~ l1_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_9]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_907,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_905,c_33,c_30,c_94,c_97]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2001,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_907]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2303,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_2001]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_16,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | v13_lattices(X1)
% 11.48/1.98      | v2_struct_0(X1) ),
% 11.48/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_975,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | v13_lattices(X1)
% 11.48/1.98      | sK5 != X1 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_976,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
% 11.48/1.98      | ~ l1_lattices(sK5)
% 11.48/1.98      | v13_lattices(sK5) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_975]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_980,plain,
% 11.48/1.98      ( m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | v13_lattices(sK5) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_976,c_30,c_94]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_981,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
% 11.48/1.98      | v13_lattices(sK5) ),
% 11.48/1.98      inference(renaming,[status(thm)],[c_980]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1998,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 11.48/1.98      | m1_subset_1(sK1(sK5,X0_55),u1_struct_0(sK5))
% 11.48/1.98      | v13_lattices(sK5) ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_981]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2306,plain,
% 11.48/1.98      ( m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | m1_subset_1(sK1(sK5,X0_55),u1_struct_0(sK5)) = iProver_top
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_26,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ v4_lattice3(X1)
% 11.48/1.98      | ~ l3_lattices(X1)
% 11.48/1.98      | v2_struct_0(X1)
% 11.48/1.98      | ~ v10_lattices(X1)
% 11.48/1.98      | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0 ),
% 11.48/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_31,negated_conjecture,
% 11.48/1.98      ( v4_lattice3(sK5) ),
% 11.48/1.98      inference(cnf_transformation,[],[f91]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_462,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ l3_lattices(X1)
% 11.48/1.98      | v2_struct_0(X1)
% 11.48/1.98      | ~ v10_lattices(X1)
% 11.48/1.98      | k15_lattice3(X1,a_2_3_lattice3(X1,X0)) = X0
% 11.48/1.98      | sK5 != X1 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_463,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ l3_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5)
% 11.48/1.98      | ~ v10_lattices(sK5)
% 11.48/1.98      | k15_lattice3(sK5,a_2_3_lattice3(sK5,X0)) = X0 ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_462]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_32,negated_conjecture,
% 11.48/1.98      ( v10_lattices(sK5) ),
% 11.48/1.98      inference(cnf_transformation,[],[f90]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_467,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | k15_lattice3(sK5,a_2_3_lattice3(sK5,X0)) = X0 ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_463,c_33,c_32,c_30]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2008,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 11.48/1.98      | k15_lattice3(sK5,a_2_3_lattice3(sK5,X0_55)) = X0_55 ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_467]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2297,plain,
% 11.48/1.98      ( k15_lattice3(sK5,a_2_3_lattice3(sK5,X0_55)) = X0_55
% 11.48/1.98      | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_2008]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2821,plain,
% 11.48/1.98      ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,X0_55))) = sK1(sK5,X0_55)
% 11.48/1.98      | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2306,c_2297]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_4233,plain,
% 11.48/1.98      ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5))
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2303,c_2821]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_24,plain,
% 11.48/1.98      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_663,plain,
% 11.48/1.98      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | sK5 != X0 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_664,plain,
% 11.48/1.98      ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
% 11.48/1.98      | v2_struct_0(sK5) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_663]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_668,plain,
% 11.48/1.98      ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5)) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_664,c_33]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2006,plain,
% 11.48/1.98      ( m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5)) ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_668]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2299,plain,
% 11.48/1.98      ( m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5)) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_17,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | ~ v13_lattices(X1)
% 11.48/1.98      | v2_struct_0(X1)
% 11.48/1.98      | k2_lattices(X1,X0,sK2(X1)) = sK2(X1) ),
% 11.48/1.98      inference(cnf_transformation,[],[f77]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_954,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | ~ v13_lattices(X1)
% 11.48/1.98      | k2_lattices(X1,X0,sK2(X1)) = sK2(X1)
% 11.48/1.98      | sK5 != X1 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_955,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ l1_lattices(sK5)
% 11.48/1.98      | ~ v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,X0,sK2(sK5)) = sK2(sK5) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_954]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_959,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,X0,sK2(sK5)) = sK2(sK5) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_955,c_30,c_94]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1999,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 11.48/1.98      | ~ v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,X0_55,sK2(sK5)) = sK2(sK5) ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_959]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2305,plain,
% 11.48/1.98      ( k2_lattices(sK5,X0_55,sK2(sK5)) = sK2(sK5)
% 11.48/1.98      | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | v13_lattices(sK5) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_1999]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2546,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),sK2(sK5)) = sK2(sK5)
% 11.48/1.98      | v13_lattices(sK5) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2299,c_2305]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_4277,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),sK2(sK5)) = sK2(sK5)
% 11.48/1.98      | k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5)) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_4233,c_2546]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_29,negated_conjecture,
% 11.48/1.98      ( ~ v13_lattices(sK5)
% 11.48/1.98      | ~ l3_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5)
% 11.48/1.98      | ~ v10_lattices(sK5)
% 11.48/1.98      | k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f93]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_197,negated_conjecture,
% 11.48/1.98      ( ~ v13_lattices(sK5)
% 11.48/1.98      | k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_29,c_33,c_32,c_30]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2009,negated_conjecture,
% 11.48/1.98      ( ~ v13_lattices(sK5)
% 11.48/1.98      | k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_197]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2025,plain,
% 11.48/1.98      ( k5_lattices(sK5) != k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | v13_lattices(sK5) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_2009]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2013,plain,
% 11.48/1.98      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 11.48/1.98      theory(equality) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2398,plain,
% 11.48/1.98      ( k15_lattice3(sK5,k1_xboole_0) != X0_55
% 11.48/1.98      | k5_lattices(sK5) != X0_55
% 11.48/1.98      | k5_lattices(sK5) = k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_2013]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2435,plain,
% 11.48/1.98      ( k15_lattice3(sK5,k1_xboole_0) != k5_lattices(sK5)
% 11.48/1.98      | k5_lattices(sK5) = k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | k5_lattices(sK5) != k5_lattices(sK5) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_2398]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2011,plain,( X0_55 = X0_55 ),theory(equality) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2551,plain,
% 11.48/1.98      ( k5_lattices(sK5) = k5_lattices(sK5) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_2011]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_8,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | ~ v13_lattices(X1)
% 11.48/1.98      | v2_struct_0(X1)
% 11.48/1.98      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
% 11.48/1.98      inference(cnf_transformation,[],[f95]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1020,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | ~ v13_lattices(X1)
% 11.48/1.98      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
% 11.48/1.98      | sK5 != X1 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1021,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
% 11.48/1.98      | ~ l1_lattices(sK5)
% 11.48/1.98      | ~ v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),X0) = k5_lattices(sK5) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_1020]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1025,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),X0) = k5_lattices(sK5) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_1021,c_33,c_30,c_94,c_97]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1996,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 11.48/1.98      | ~ v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),X0_55) = k5_lattices(sK5) ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_1025]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2308,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),X0_55) = k5_lattices(sK5)
% 11.48/1.98      | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | v13_lattices(sK5) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_1996]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2583,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5)
% 11.48/1.98      | v13_lattices(sK5) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2299,c_2308]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_4276,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5)
% 11.48/1.98      | k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5)) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_4233,c_2583]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_23,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | ~ v6_lattices(X1)
% 11.48/1.98      | v2_struct_0(X1)
% 11.48/1.98      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 11.48/1.98      inference(cnf_transformation,[],[f80]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_915,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | ~ v6_lattices(X1)
% 11.48/1.98      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 11.48/1.98      | sK5 != X1 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_916,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | ~ l1_lattices(sK5)
% 11.48/1.98      | ~ v6_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,X0,X1) = k2_lattices(sK5,X1,X0) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_915]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3,plain,
% 11.48/1.98      ( v6_lattices(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | ~ v10_lattices(X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_508,plain,
% 11.48/1.98      ( v6_lattices(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | sK5 != X0 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_3,c_32]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_509,plain,
% 11.48/1.98      ( v6_lattices(sK5) | ~ l3_lattices(sK5) | v2_struct_0(sK5) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_508]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_113,plain,
% 11.48/1.98      ( v6_lattices(sK5)
% 11.48/1.98      | ~ l3_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5)
% 11.48/1.98      | ~ v10_lattices(sK5) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_511,plain,
% 11.48/1.98      ( v6_lattices(sK5) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_509,c_33,c_32,c_30,c_113]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_842,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | v2_struct_0(X1)
% 11.48/1.98      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 11.48/1.98      | sK5 != X1 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_23,c_511]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_843,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | ~ l1_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5)
% 11.48/1.98      | k2_lattices(sK5,X0,X1) = k2_lattices(sK5,X1,X0) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_842]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_847,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | k2_lattices(sK5,X0,X1) = k2_lattices(sK5,X1,X0) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_843,c_33,c_30,c_94]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_919,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | k2_lattices(sK5,X0,X1) = k2_lattices(sK5,X1,X0) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_916,c_33,c_30,c_94,c_843]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2003,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X1_55,u1_struct_0(sK5))
% 11.48/1.98      | k2_lattices(sK5,X0_55,X1_55) = k2_lattices(sK5,X1_55,X0_55) ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_919]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2301,plain,
% 11.48/1.98      ( k2_lattices(sK5,X0_55,X1_55) = k2_lattices(sK5,X1_55,X0_55)
% 11.48/1.98      | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | m1_subset_1(X1_55,u1_struct_0(sK5)) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_2003]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2709,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),X0_55) = k2_lattices(sK5,X0_55,k5_lattices(sK5))
% 11.48/1.98      | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2303,c_2301]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3605,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k2_lattices(sK5,k15_lattice3(sK5,X0_58),k5_lattices(sK5)) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2299,c_2709]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2440,plain,
% 11.48/1.98      ( k15_lattice3(sK5,a_2_3_lattice3(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2303,c_2297]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_14,plain,
% 11.48/1.98      ( ~ r1_lattices(X0,X1,X2)
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.48/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.48/1.98      | ~ v8_lattices(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | ~ v9_lattices(X0)
% 11.48/1.98      | k2_lattices(X0,X1,X2) = X1 ),
% 11.48/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1,plain,
% 11.48/1.98      ( ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | ~ v10_lattices(X0)
% 11.48/1.98      | v9_lattices(X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f64]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_530,plain,
% 11.48/1.98      ( ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | v9_lattices(X0)
% 11.48/1.98      | sK5 != X0 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_1,c_32]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_531,plain,
% 11.48/1.98      ( ~ l3_lattices(sK5) | v2_struct_0(sK5) | v9_lattices(sK5) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_530]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_119,plain,
% 11.48/1.98      ( ~ l3_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5)
% 11.48/1.98      | ~ v10_lattices(sK5)
% 11.48/1.98      | v9_lattices(sK5) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_533,plain,
% 11.48/1.98      ( v9_lattices(sK5) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_531,c_33,c_32,c_30,c_119]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_547,plain,
% 11.48/1.98      ( ~ r1_lattices(X0,X1,X2)
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.48/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.48/1.98      | ~ v8_lattices(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | k2_lattices(X0,X1,X2) = X1
% 11.48/1.98      | sK5 != X0 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_14,c_533]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_548,plain,
% 11.48/1.98      ( ~ r1_lattices(sK5,X0,X1)
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ v8_lattices(sK5)
% 11.48/1.98      | ~ l3_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5)
% 11.48/1.98      | k2_lattices(sK5,X0,X1) = X0 ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_547]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2,plain,
% 11.48/1.98      ( v8_lattices(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | ~ v10_lattices(X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_116,plain,
% 11.48/1.98      ( v8_lattices(sK5)
% 11.48/1.98      | ~ l3_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5)
% 11.48/1.98      | ~ v10_lattices(sK5) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_552,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | ~ r1_lattices(sK5,X0,X1)
% 11.48/1.98      | k2_lattices(sK5,X0,X1) = X0 ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_548,c_33,c_32,c_30,c_116]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_553,plain,
% 11.48/1.98      ( ~ r1_lattices(sK5,X0,X1)
% 11.48/1.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | k2_lattices(sK5,X0,X1) = X0 ),
% 11.48/1.98      inference(renaming,[status(thm)],[c_552]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_0,plain,
% 11.48/1.98      ( r1_tarski(k1_xboole_0,X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_28,plain,
% 11.48/1.98      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 11.48/1.98      | ~ r1_tarski(X1,X2)
% 11.48/1.98      | ~ v4_lattice3(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | ~ v10_lattices(X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_399,plain,
% 11.48/1.98      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 11.48/1.98      | ~ v4_lattice3(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | ~ v10_lattices(X0)
% 11.48/1.98      | X2 != X3
% 11.48/1.98      | k1_xboole_0 != X1 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_400,plain,
% 11.48/1.98      ( r3_lattices(X0,k15_lattice3(X0,k1_xboole_0),k15_lattice3(X0,X1))
% 11.48/1.98      | ~ v4_lattice3(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | ~ v10_lattices(X0) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_399]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_432,plain,
% 11.48/1.98      ( r3_lattices(X0,k15_lattice3(X0,k1_xboole_0),k15_lattice3(X0,X1))
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | ~ v10_lattices(X0)
% 11.48/1.98      | sK5 != X0 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_400,c_31]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_433,plain,
% 11.48/1.98      ( r3_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0))
% 11.48/1.98      | ~ l3_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5)
% 11.48/1.98      | ~ v10_lattices(sK5) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_432]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_437,plain,
% 11.48/1.98      ( r3_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_433,c_33,c_32,c_30]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_12,plain,
% 11.48/1.98      ( r1_lattices(X0,X1,X2)
% 11.48/1.98      | ~ r3_lattices(X0,X1,X2)
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.48/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.48/1.98      | ~ v6_lattices(X0)
% 11.48/1.98      | ~ v8_lattices(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | ~ v9_lattices(X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f71]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_595,plain,
% 11.48/1.98      ( r1_lattices(X0,X1,X2)
% 11.48/1.98      | ~ r3_lattices(X0,X1,X2)
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.48/1.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.48/1.98      | ~ v6_lattices(X0)
% 11.48/1.98      | ~ v8_lattices(X0)
% 11.48/1.98      | ~ l3_lattices(X0)
% 11.48/1.98      | v2_struct_0(X0)
% 11.48/1.98      | sK5 != X0 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_12,c_533]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_596,plain,
% 11.48/1.98      ( r1_lattices(sK5,X0,X1)
% 11.48/1.98      | ~ r3_lattices(sK5,X0,X1)
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ v6_lattices(sK5)
% 11.48/1.98      | ~ v8_lattices(sK5)
% 11.48/1.98      | ~ l3_lattices(sK5)
% 11.48/1.98      | v2_struct_0(sK5) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_595]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_600,plain,
% 11.48/1.98      ( r1_lattices(sK5,X0,X1)
% 11.48/1.98      | ~ r3_lattices(sK5,X0,X1)
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_596,c_33,c_32,c_30,c_113,c_116]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_601,plain,
% 11.48/1.98      ( r1_lattices(sK5,X0,X1)
% 11.48/1.98      | ~ r3_lattices(sK5,X0,X1)
% 11.48/1.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 11.48/1.98      inference(renaming,[status(thm)],[c_600]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_690,plain,
% 11.48/1.98      ( r1_lattices(sK5,X0,X1)
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | k15_lattice3(sK5,X2) != X1
% 11.48/1.98      | k15_lattice3(sK5,k1_xboole_0) != X0
% 11.48/1.98      | sK5 != sK5 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_437,c_601]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_691,plain,
% 11.48/1.98      ( r1_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0))
% 11.48/1.98      | ~ m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5)) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_690]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_695,plain,
% 11.48/1.98      ( r1_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0))
% 11.48/1.98      | ~ m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5)) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_691,c_33,c_664]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_705,plain,
% 11.48/1.98      ( r1_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) ),
% 11.48/1.98      inference(forward_subsumption_resolution,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_695,c_668]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_732,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 11.48/1.98      | k2_lattices(sK5,X0,X1) = X0
% 11.48/1.98      | k15_lattice3(sK5,X2) != X1
% 11.48/1.98      | k15_lattice3(sK5,k1_xboole_0) != X0
% 11.48/1.98      | sK5 != sK5 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_553,c_705]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_733,plain,
% 11.48/1.98      ( ~ m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
% 11.48/1.98      | ~ m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5))
% 11.48/1.98      | k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) = k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_732]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_737,plain,
% 11.48/1.98      ( ~ m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5))
% 11.48/1.98      | k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) = k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_733,c_33,c_664]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_747,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0)) = k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(forward_subsumption_resolution,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_737,c_668]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2005,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k15_lattice3(sK5,X0_58)) = k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_747]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2894,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),k5_lattices(sK5)) = k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2440,c_2005]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3644,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_3605,c_2894]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_18410,plain,
% 11.48/1.98      ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5))
% 11.48/1.98      | k15_lattice3(sK5,k1_xboole_0) = k5_lattices(sK5) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_4276,c_3644]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_20035,plain,
% 11.48/1.98      ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5)))) = sK1(sK5,k5_lattices(sK5)) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_4277,c_2025,c_2435,c_2551,c_4233,c_18410]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_4236,plain,
% 11.48/1.98      ( k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)))) = sK1(sK5,k15_lattice3(sK5,X0_58))
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2299,c_2821]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_4336,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5)
% 11.48/1.98      | k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k15_lattice3(sK5,X1_58)))) = sK1(sK5,k15_lattice3(sK5,X1_58)) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_4236,c_2583]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_27331,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,k15_lattice3(sK5,X0_58))) = k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X1_58)) = k5_lattices(sK5) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_4336,c_2005]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_27620,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,sK1(sK5,k5_lattices(sK5)))) = k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_20035,c_27331]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_34,plain,
% 11.48/1.98      ( v2_struct_0(sK5) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_37,plain,
% 11.48/1.98      ( l3_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_93,plain,
% 11.48/1.98      ( l1_lattices(X0) = iProver_top | l3_lattices(X0) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_95,plain,
% 11.48/1.98      ( l1_lattices(sK5) = iProver_top
% 11.48/1.98      | l3_lattices(sK5) != iProver_top ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_93]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_96,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) = iProver_top
% 11.48/1.98      | l1_lattices(X0) != iProver_top
% 11.48/1.98      | v2_struct_0(X0) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_98,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) = iProver_top
% 11.48/1.98      | l1_lattices(sK5) != iProver_top
% 11.48/1.98      | v2_struct_0(sK5) = iProver_top ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_96]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_27616,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,k15_lattice3(sK5,X0_58))) = k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_20035,c_27331]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2032,plain,
% 11.48/1.98      ( m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5)) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2034,plain,
% 11.48/1.98      ( m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5)) = iProver_top ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_2032]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_15,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | v13_lattices(X1)
% 11.48/1.98      | v2_struct_0(X1)
% 11.48/1.98      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 11.48/1.98      | k2_lattices(X1,sK1(X1,X0),X0) != X0 ),
% 11.48/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_996,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.48/1.98      | ~ l1_lattices(X1)
% 11.48/1.98      | v13_lattices(X1)
% 11.48/1.98      | k2_lattices(X1,X0,sK1(X1,X0)) != X0
% 11.48/1.98      | k2_lattices(X1,sK1(X1,X0),X0) != X0
% 11.48/1.98      | sK5 != X1 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_15,c_33]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_997,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | ~ l1_lattices(sK5)
% 11.48/1.98      | v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,X0,sK1(sK5,X0)) != X0
% 11.48/1.98      | k2_lattices(sK5,sK1(sK5,X0),X0) != X0 ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_996]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1001,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 11.48/1.98      | v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,X0,sK1(sK5,X0)) != X0
% 11.48/1.98      | k2_lattices(sK5,sK1(sK5,X0),X0) != X0 ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_997,c_30,c_94]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1997,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 11.48/1.98      | v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,X0_55,sK1(sK5,X0_55)) != X0_55
% 11.48/1.98      | k2_lattices(sK5,sK1(sK5,X0_55),X0_55) != X0_55 ),
% 11.48/1.98      inference(subtyping,[status(esa)],[c_1001]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2378,plain,
% 11.48/1.98      ( ~ m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5))
% 11.48/1.98      | v13_lattices(sK5)
% 11.48/1.98      | k2_lattices(sK5,k15_lattice3(sK5,X0_58),sK1(sK5,k15_lattice3(sK5,X0_58))) != k15_lattice3(sK5,X0_58)
% 11.48/1.98      | k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)),k15_lattice3(sK5,X0_58)) != k15_lattice3(sK5,X0_58) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1997]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2379,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),sK1(sK5,k15_lattice3(sK5,X0_58))) != k15_lattice3(sK5,X0_58)
% 11.48/1.98      | k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)),k15_lattice3(sK5,X0_58)) != k15_lattice3(sK5,X0_58)
% 11.48/1.98      | m1_subset_1(k15_lattice3(sK5,X0_58),u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_2378]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2381,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,k15_lattice3(sK5,k1_xboole_0))) != k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,k1_xboole_0)),k15_lattice3(sK5,k1_xboole_0)) != k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | m1_subset_1(k15_lattice3(sK5,k1_xboole_0),u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_2379]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_20045,plain,
% 11.48/1.98      ( m1_subset_1(sK1(sK5,k5_lattices(sK5)),u1_struct_0(sK5)) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_20035,c_2299]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_20188,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5)
% 11.48/1.98      | v13_lattices(sK5) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_20045,c_2308]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_27625,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,k1_xboole_0),sK1(sK5,k15_lattice3(sK5,k1_xboole_0))) = k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_27616]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2710,plain,
% 11.48/1.98      ( k2_lattices(sK5,X0_55,k15_lattice3(sK5,X0_58)) = k2_lattices(sK5,k15_lattice3(sK5,X0_58),X0_55)
% 11.48/1.98      | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2299,c_2301]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3824,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),k15_lattice3(sK5,X1_58)) = k2_lattices(sK5,k15_lattice3(sK5,X1_58),k15_lattice3(sK5,X0_58)) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2299,c_2710]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3842,plain,
% 11.48/1.98      ( k2_lattices(sK5,k15_lattice3(sK5,X0_58),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_3824,c_2005]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_27326,plain,
% 11.48/1.98      ( k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X1_58)) = k5_lattices(sK5) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_4336,c_3842]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_29179,plain,
% 11.48/1.98      ( k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,X0_58)),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_20035,c_27326]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_29191,plain,
% 11.48/1.98      ( k2_lattices(sK5,sK1(sK5,k15_lattice3(sK5,k1_xboole_0)),k15_lattice3(sK5,k1_xboole_0)) = k15_lattice3(sK5,k1_xboole_0)
% 11.48/1.98      | k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_29179]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_29197,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_27616,c_2034,c_2381,c_20188,c_27625,c_29191]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2307,plain,
% 11.48/1.98      ( k2_lattices(sK5,X0_55,sK1(sK5,X0_55)) != X0_55
% 11.48/1.98      | k2_lattices(sK5,sK1(sK5,X0_55),X0_55) != X0_55
% 11.48/1.98      | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_1997]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_29199,plain,
% 11.48/1.98      ( k2_lattices(sK5,sK1(sK5,k5_lattices(sK5)),k5_lattices(sK5)) != k5_lattices(sK5)
% 11.48/1.98      | m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_29197,c_2307]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_20042,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,a_2_3_lattice3(sK5,sK1(sK5,k5_lattices(sK5))))) = k2_lattices(sK5,sK1(sK5,k5_lattices(sK5)),k5_lattices(sK5)) ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_20035,c_3605]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_20051,plain,
% 11.48/1.98      ( k2_lattices(sK5,sK1(sK5,k5_lattices(sK5)),k5_lattices(sK5)) = k2_lattices(sK5,k5_lattices(sK5),sK1(sK5,k5_lattices(sK5))) ),
% 11.48/1.98      inference(demodulation,[status(thm)],[c_20042,c_20035]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_29200,plain,
% 11.48/1.98      ( k5_lattices(sK5) != k5_lattices(sK5)
% 11.48/1.98      | m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(light_normalisation,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_29199,c_20051,c_29197]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_29201,plain,
% 11.48/1.98      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) != iProver_top
% 11.48/1.98      | v13_lattices(sK5) = iProver_top ),
% 11.48/1.98      inference(equality_resolution_simp,[status(thm)],[c_29200]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_29348,plain,
% 11.48/1.98      ( k2_lattices(sK5,k5_lattices(sK5),k15_lattice3(sK5,X0_58)) = k5_lattices(sK5) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_27620,c_34,c_37,c_95,c_98,c_2583,c_29201]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_29353,plain,
% 11.48/1.98      ( k15_lattice3(sK5,k1_xboole_0) = k5_lattices(sK5) ),
% 11.48/1.98      inference(demodulation,[status(thm)],[c_29348,c_3644]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(contradiction,plain,
% 11.48/1.98      ( $false ),
% 11.48/1.98      inference(minisat,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_29353,c_29201,c_2551,c_2435,c_2025,c_98,c_95,c_37,
% 11.48/1.98                 c_34]) ).
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.48/1.98  
% 11.48/1.98  ------                               Statistics
% 11.48/1.98  
% 11.48/1.98  ------ General
% 11.48/1.98  
% 11.48/1.98  abstr_ref_over_cycles:                  0
% 11.48/1.98  abstr_ref_under_cycles:                 0
% 11.48/1.98  gc_basic_clause_elim:                   0
% 11.48/1.98  forced_gc_time:                         0
% 11.48/1.98  parsing_time:                           0.009
% 11.48/1.98  unif_index_cands_time:                  0.
% 11.48/1.98  unif_index_add_time:                    0.
% 11.48/1.98  orderings_time:                         0.
% 11.48/1.98  out_proof_time:                         0.019
% 11.48/1.98  total_time:                             1.288
% 11.48/1.98  num_of_symbols:                         59
% 11.48/1.98  num_of_terms:                           24196
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing
% 11.48/1.98  
% 11.48/1.98  num_of_splits:                          0
% 11.48/1.98  num_of_split_atoms:                     0
% 11.48/1.98  num_of_reused_defs:                     0
% 11.48/1.98  num_eq_ax_congr_red:                    43
% 11.48/1.98  num_of_sem_filtered_clauses:            1
% 11.48/1.98  num_of_subtypes:                        4
% 11.48/1.98  monotx_restored_types:                  0
% 11.48/1.98  sat_num_of_epr_types:                   0
% 11.48/1.98  sat_num_of_non_cyclic_types:            0
% 11.48/1.98  sat_guarded_non_collapsed_types:        1
% 11.48/1.98  num_pure_diseq_elim:                    0
% 11.48/1.98  simp_replaced_by:                       0
% 11.48/1.98  res_preprocessed:                       99
% 11.48/1.98  prep_upred:                             0
% 11.48/1.98  prep_unflattend:                        43
% 11.48/1.98  smt_new_axioms:                         0
% 11.48/1.98  pred_elim_cands:                        2
% 11.48/1.98  pred_elim:                              11
% 11.48/1.98  pred_elim_cl:                           16
% 11.48/1.98  pred_elim_cycles:                       14
% 11.48/1.98  merged_defs:                            0
% 11.48/1.98  merged_defs_ncl:                        0
% 11.48/1.98  bin_hyper_res:                          0
% 11.48/1.98  prep_cycles:                            4
% 11.48/1.98  pred_elim_time:                         0.025
% 11.48/1.98  splitting_time:                         0.
% 11.48/1.98  sem_filter_time:                        0.
% 11.48/1.98  monotx_time:                            0.
% 11.48/1.98  subtype_inf_time:                       0.
% 11.48/1.98  
% 11.48/1.98  ------ Problem properties
% 11.48/1.98  
% 11.48/1.98  clauses:                                17
% 11.48/1.98  conjectures:                            1
% 11.48/1.98  epr:                                    0
% 11.48/1.98  horn:                                   15
% 11.48/1.98  ground:                                 3
% 11.48/1.98  unary:                                  3
% 11.48/1.98  binary:                                 4
% 11.48/1.98  lits:                                   45
% 11.48/1.98  lits_eq:                                16
% 11.48/1.98  fd_pure:                                0
% 11.48/1.98  fd_pseudo:                              0
% 11.48/1.98  fd_cond:                                2
% 11.48/1.98  fd_pseudo_cond:                         0
% 11.48/1.98  ac_symbols:                             0
% 11.48/1.98  
% 11.48/1.98  ------ Propositional Solver
% 11.48/1.98  
% 11.48/1.98  prop_solver_calls:                      32
% 11.48/1.98  prop_fast_solver_calls:                 2069
% 11.48/1.98  smt_solver_calls:                       0
% 11.48/1.98  smt_fast_solver_calls:                  0
% 11.48/1.98  prop_num_of_clauses:                    18135
% 11.48/1.98  prop_preprocess_simplified:             20881
% 11.48/1.98  prop_fo_subsumed:                       93
% 11.48/1.98  prop_solver_time:                       0.
% 11.48/1.98  smt_solver_time:                        0.
% 11.48/1.98  smt_fast_solver_time:                   0.
% 11.48/1.98  prop_fast_solver_time:                  0.
% 11.48/1.98  prop_unsat_core_time:                   0.001
% 11.48/1.98  
% 11.48/1.98  ------ QBF
% 11.48/1.98  
% 11.48/1.98  qbf_q_res:                              0
% 11.48/1.98  qbf_num_tautologies:                    0
% 11.48/1.98  qbf_prep_cycles:                        0
% 11.48/1.98  
% 11.48/1.98  ------ BMC1
% 11.48/1.98  
% 11.48/1.98  bmc1_current_bound:                     -1
% 11.48/1.98  bmc1_last_solved_bound:                 -1
% 11.48/1.98  bmc1_unsat_core_size:                   -1
% 11.48/1.98  bmc1_unsat_core_parents_size:           -1
% 11.48/1.98  bmc1_merge_next_fun:                    0
% 11.48/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.48/1.98  
% 11.48/1.98  ------ Instantiation
% 11.48/1.98  
% 11.48/1.98  inst_num_of_clauses:                    4525
% 11.48/1.98  inst_num_in_passive:                    1345
% 11.48/1.98  inst_num_in_active:                     1582
% 11.48/1.98  inst_num_in_unprocessed:                1598
% 11.48/1.98  inst_num_of_loops:                      1700
% 11.48/1.98  inst_num_of_learning_restarts:          0
% 11.48/1.98  inst_num_moves_active_passive:          116
% 11.48/1.98  inst_lit_activity:                      0
% 11.48/1.98  inst_lit_activity_moves:                1
% 11.48/1.98  inst_num_tautologies:                   0
% 11.48/1.98  inst_num_prop_implied:                  0
% 11.48/1.98  inst_num_existing_simplified:           0
% 11.48/1.98  inst_num_eq_res_simplified:             0
% 11.48/1.98  inst_num_child_elim:                    0
% 11.48/1.98  inst_num_of_dismatching_blockings:      1184
% 11.48/1.98  inst_num_of_non_proper_insts:           3702
% 11.48/1.98  inst_num_of_duplicates:                 0
% 11.48/1.98  inst_inst_num_from_inst_to_res:         0
% 11.48/1.98  inst_dismatching_checking_time:         0.
% 11.48/1.98  
% 11.48/1.98  ------ Resolution
% 11.48/1.98  
% 11.48/1.98  res_num_of_clauses:                     0
% 11.48/1.98  res_num_in_passive:                     0
% 11.48/1.98  res_num_in_active:                      0
% 11.48/1.98  res_num_of_loops:                       103
% 11.48/1.98  res_forward_subset_subsumed:            214
% 11.48/1.98  res_backward_subset_subsumed:           0
% 11.48/1.98  res_forward_subsumed:                   0
% 11.48/1.98  res_backward_subsumed:                  0
% 11.48/1.98  res_forward_subsumption_resolution:     2
% 11.48/1.98  res_backward_subsumption_resolution:    0
% 11.48/1.98  res_clause_to_clause_subsumption:       9128
% 11.48/1.98  res_orphan_elimination:                 0
% 11.48/1.98  res_tautology_del:                      145
% 11.48/1.98  res_num_eq_res_simplified:              0
% 11.48/1.98  res_num_sel_changes:                    0
% 11.48/1.98  res_moves_from_active_to_pass:          0
% 11.48/1.98  
% 11.48/1.98  ------ Superposition
% 11.48/1.98  
% 11.48/1.98  sup_time_total:                         0.
% 11.48/1.98  sup_time_generating:                    0.
% 11.48/1.98  sup_time_sim_full:                      0.
% 11.48/1.98  sup_time_sim_immed:                     0.
% 11.48/1.98  
% 11.48/1.98  sup_num_of_clauses:                     3525
% 11.48/1.98  sup_num_in_active:                      246
% 11.48/1.98  sup_num_in_passive:                     3279
% 11.48/1.98  sup_num_of_loops:                       338
% 11.48/1.98  sup_fw_superposition:                   2049
% 11.48/1.98  sup_bw_superposition:                   2557
% 11.48/1.98  sup_immediate_simplified:               316
% 11.48/1.98  sup_given_eliminated:                   0
% 11.48/1.98  comparisons_done:                       0
% 11.48/1.98  comparisons_avoided:                    315
% 11.48/1.98  
% 11.48/1.98  ------ Simplifications
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  sim_fw_subset_subsumed:                 148
% 11.48/1.98  sim_bw_subset_subsumed:                 285
% 11.48/1.98  sim_fw_subsumed:                        115
% 11.48/1.98  sim_bw_subsumed:                        36
% 11.48/1.98  sim_fw_subsumption_res:                 0
% 11.48/1.98  sim_bw_subsumption_res:                 0
% 11.48/1.98  sim_tautology_del:                      130
% 11.48/1.98  sim_eq_tautology_del:                   71
% 11.48/1.98  sim_eq_res_simp:                        1
% 11.48/1.98  sim_fw_demodulated:                     16
% 11.48/1.98  sim_bw_demodulated:                     37
% 11.48/1.98  sim_light_normalised:                   56
% 11.48/1.98  sim_joinable_taut:                      0
% 11.48/1.98  sim_joinable_simp:                      0
% 11.48/1.98  sim_ac_normalised:                      0
% 11.48/1.98  sim_smt_subsumption:                    0
% 11.48/1.98  
%------------------------------------------------------------------------------
