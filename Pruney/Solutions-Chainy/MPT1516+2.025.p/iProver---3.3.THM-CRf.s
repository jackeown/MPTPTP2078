%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:21 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  279 (3698 expanded)
%              Number of clauses        :  176 (1063 expanded)
%              Number of leaves         :   27 ( 726 expanded)
%              Depth                    :   27
%              Number of atoms          : 1333 (24187 expanded)
%              Number of equality atoms :  387 (3399 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :   11 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f78,plain,
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

fof(f79,plain,
    ( ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
      | ~ l3_lattices(sK9)
      | ~ v13_lattices(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) )
    & l3_lattices(sK9)
    & v4_lattice3(sK9)
    & v10_lattices(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f50,f78])).

fof(f125,plain,(
    l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f79])).

fof(f122,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f79])).

fof(f11,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( k2_lattices(X0,X4,sK3(X0)) = sK3(X0)
              & k2_lattices(X0,sK3(X0),X4) = sK3(X0) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( k2_lattices(X0,X4,sK3(X0)) = sK3(X0)
                  & k2_lattices(X0,sK3(X0),X4) = sK3(X0) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f62,f64,f63])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f96,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
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

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f124,plain,(
    v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f79])).

fof(f123,plain,(
    v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f79])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f43])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X1,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r3_lattices(X1,X6,X5)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f71])).

fof(f74,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,X6,X5)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK7(X0,X1,X2),X2)
        & r3_lattices(X1,sK7(X0,X1,X2),X5)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r3_lattices(X1,X6,X5)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r3_lattices(X1,X6,sK6(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK6(X0,X1,X2) = X0
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X2)
            & r3_lattices(X1,sK7(X0,X1,X2),sK6(X0,X1,X2))
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
            & sK6(X0,X1,X2) = X0
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f72,f74,f73])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f103,plain,(
    ! [X4,X0] :
      ( k2_lattices(X0,X4,sK3(X0)) = sK3(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f128,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f126,plain,
    ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
    | ~ l3_lattices(sK9)
    | ~ v13_lattices(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f79])).

fof(f6,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f130,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
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

fof(f39,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f69,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,sK5(X0)) != k2_lattices(X0,sK5(X0),X1)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
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

fof(f70,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f67,f69,f68])).

fof(f106,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f5,axiom,(
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

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f88,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f76,plain,(
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

fof(f77,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f76])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f127,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f85])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_43,negated_conjecture,
    ( l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1206,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_43])).

cnf(c_1207,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_1206])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1211,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1207,c_46])).

cnf(c_3075,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1432,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_46])).

cnf(c_1433,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | m1_subset_1(sK2(sK9,X0),u1_struct_0(sK9))
    | ~ l1_lattices(sK9)
    | v13_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1432])).

cnf(c_16,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1221,plain,
    ( l1_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_43])).

cnf(c_1222,plain,
    ( l1_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1221])).

cnf(c_1437,plain,
    ( m1_subset_1(sK2(sK9,X0),u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | v13_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1433,c_1222])).

cnf(c_1438,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | m1_subset_1(sK2(sK9,X0),u1_struct_0(sK9))
    | v13_lattices(sK9) ),
    inference(renaming,[status(thm)],[c_1437])).

cnf(c_3069,plain,
    ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9,X0),u1_struct_0(sK9)) = iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1438])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_44,negated_conjecture,
    ( v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_884,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_44])).

cnf(c_885,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_45,negated_conjecture,
    ( v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_885,c_46,c_45,c_43])).

cnf(c_3088,plain,
    ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_4528,plain,
    ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),sK2(sK9,X0))) = sK2(sK9,X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3069,c_3088])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
    | r2_hidden(sK7(X0,X1,X2),X2)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_974,plain,
    ( ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
    | r2_hidden(sK7(X0,X1,X2),X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_44])).

cnf(c_975,plain,
    ( ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1))
    | r2_hidden(sK7(X0,sK9,X1),X1)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_979,plain,
    ( r2_hidden(sK7(X0,sK9,X1),X1)
    | ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_46,c_45,c_43])).

cnf(c_980,plain,
    ( ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1))
    | r2_hidden(sK7(X0,sK9,X1),X1) ),
    inference(renaming,[status(thm)],[c_979])).

cnf(c_3083,plain,
    ( r2_hidden(X0,a_2_6_lattice3(sK9,X1)) != iProver_top
    | r2_hidden(sK7(X0,sK9,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_34,plain,
    ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_956,plain,
    ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_44])).

cnf(c_957,plain,
    ( m1_subset_1(sK7(X0,sK9,X1),u1_struct_0(sK9))
    | ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_956])).

cnf(c_961,plain,
    ( ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1))
    | m1_subset_1(sK7(X0,sK9,X1),u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_957,c_46,c_45,c_43])).

cnf(c_962,plain,
    ( m1_subset_1(sK7(X0,sK9,X1),u1_struct_0(sK9))
    | ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1)) ),
    inference(renaming,[status(thm)],[c_961])).

cnf(c_3084,plain,
    ( m1_subset_1(sK7(X0,sK9,X1),u1_struct_0(sK9)) = iProver_top
    | r2_hidden(X0,a_2_6_lattice3(sK9,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK3(X1)) = sK3(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1411,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,X0,sK3(X1)) = sK3(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_46])).

cnf(c_1412,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l1_lattices(sK9)
    | ~ v13_lattices(sK9)
    | k2_lattices(sK9,X0,sK3(sK9)) = sK3(sK9) ),
    inference(unflattening,[status(thm)],[c_1411])).

cnf(c_1416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | k2_lattices(sK9,X0,sK3(sK9)) = sK3(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1412,c_1222])).

cnf(c_3070,plain,
    ( k2_lattices(sK9,X0,sK3(sK9)) = sK3(sK9)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1416])).

cnf(c_3782,plain,
    ( k2_lattices(sK9,sK7(X0,sK9,X1),sK3(sK9)) = sK3(sK9)
    | r2_hidden(X0,a_2_6_lattice3(sK9,X1)) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3084,c_3070])).

cnf(c_5887,plain,
    ( k2_lattices(sK9,sK7(sK7(X0,sK9,a_2_6_lattice3(sK9,X1)),sK9,X1),sK3(sK9)) = sK3(sK9)
    | r2_hidden(X0,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_3782])).

cnf(c_6346,plain,
    ( k2_lattices(sK9,sK7(sK7(sK7(X0,sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))),sK9,a_2_6_lattice3(sK9,X1)),sK9,X1),sK3(sK9)) = sK3(sK9)
    | r2_hidden(X0,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1)))) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_5887])).

cnf(c_7183,plain,
    ( k2_lattices(sK9,sK7(sK7(sK7(sK7(X0,sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1)))),sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))),sK9,a_2_6_lattice3(sK9,X1)),sK9,X1),sK3(sK9)) = sK3(sK9)
    | r2_hidden(X0,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))))) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_6346])).

cnf(c_9688,plain,
    ( k2_lattices(sK9,sK7(sK7(sK7(sK7(sK7(X0,sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))))),sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1)))),sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))),sK9,a_2_6_lattice3(sK9,X1)),sK9,X1),sK3(sK9)) = sK3(sK9)
    | r2_hidden(X0,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1)))))) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_7183])).

cnf(c_47,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_158,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_159,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_42,negated_conjecture,
    ( ~ v13_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_262,negated_conjecture,
    ( ~ v13_lattices(sK9)
    | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42,c_46,c_45,c_43])).

cnf(c_264,plain,
    ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
    | v13_lattices(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_1208,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_1210,plain,
    ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1208])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1477,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_46])).

cnf(c_1478,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | ~ l1_lattices(sK9)
    | ~ v13_lattices(sK9)
    | k2_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1477])).

cnf(c_15,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1360,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_46])).

cnf(c_1361,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | ~ l1_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1360])).

cnf(c_1482,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | k2_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1478,c_1222,c_1361])).

cnf(c_3364,plain,
    ( ~ m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
    | ~ v13_lattices(sK9)
    | k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) = k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_3365,plain,
    ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) = k5_lattices(sK9)
    | m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3364])).

cnf(c_3367,plain,
    ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0)) = k5_lattices(sK9)
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3365])).

cnf(c_2545,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3806,plain,
    ( k5_lattices(sK9) = k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_2545])).

cnf(c_2546,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3569,plain,
    ( X0 != X1
    | k5_lattices(sK9) != X1
    | k5_lattices(sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_4027,plain,
    ( X0 != k5_lattices(sK9)
    | k5_lattices(sK9) = X0
    | k5_lattices(sK9) != k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_4574,plain,
    ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) != k5_lattices(sK9)
    | k5_lattices(sK9) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0))
    | k5_lattices(sK9) != k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_4027])).

cnf(c_4575,plain,
    ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0)) != k5_lattices(sK9)
    | k5_lattices(sK9) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0))
    | k5_lattices(sK9) != k5_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_4574])).

cnf(c_1363,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1361,c_1222])).

cnf(c_3072,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1363])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1371,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_46])).

cnf(c_1372,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l1_lattices(sK9)
    | ~ v6_lattices(sK9)
    | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1371])).

cnf(c_9,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1183,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_45])).

cnf(c_1184,plain,
    ( v6_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_1183])).

cnf(c_1186,plain,
    ( v6_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1184,c_46,c_43])).

cnf(c_1298,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1186])).

cnf(c_1299,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l1_lattices(sK9)
    | v2_struct_0(sK9)
    | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_1303,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1299,c_46,c_1222])).

cnf(c_1376,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1372,c_46,c_1222,c_1299])).

cnf(c_3074,plain,
    ( k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1376])).

cnf(c_3940,plain,
    ( k2_lattices(sK9,X0,k5_lattices(sK9)) = k2_lattices(sK9,k5_lattices(sK9),X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3072,c_3074])).

cnf(c_5212,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0),k5_lattices(sK9)) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) ),
    inference(superposition,[status(thm)],[c_3075,c_3940])).

cnf(c_3413,plain,
    ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),k5_lattices(sK9))) = k5_lattices(sK9) ),
    inference(superposition,[status(thm)],[c_3072,c_3088])).

cnf(c_40,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK8(X0,X1,X2),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1010,plain,
    ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
    | r2_hidden(sK8(X0,X1,X2),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_44])).

cnf(c_1011,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1))
    | r2_hidden(sK8(sK9,X0,X1),X0)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1010])).

cnf(c_1015,plain,
    ( r2_hidden(sK8(sK9,X0,X1),X0)
    | r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1011,c_46,c_45,c_43])).

cnf(c_1016,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1))
    | r2_hidden(sK8(sK9,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_1015])).

cnf(c_3081,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1)) = iProver_top
    | r2_hidden(sK8(sK9,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3092,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4062,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3092])).

cnf(c_4464,plain,
    ( r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_4062])).

cnf(c_7,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_18,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_593,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_7,c_18])).

cnf(c_8,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_597,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_9,c_8])).

cnf(c_20,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_529,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_20])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_lattices(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_529,c_8])).

cnf(c_534,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(renaming,[status(thm)],[c_533])).

cnf(c_815,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(resolution,[status(thm)],[c_597,c_534])).

cnf(c_1159,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_815,c_45])).

cnf(c_1160,plain,
    ( ~ r3_lattices(sK9,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k2_lattices(sK9,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1159])).

cnf(c_1164,plain,
    ( ~ r3_lattices(sK9,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1160,c_46,c_43])).

cnf(c_1165,plain,
    ( ~ r3_lattices(sK9,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1164])).

cnf(c_3076,plain,
    ( k2_lattices(sK9,X0,X1) = X0
    | r3_lattices(sK9,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_4542,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0)) = k15_lattice3(sK9,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4464,c_3076])).

cnf(c_4904,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4542,c_47,c_1208,c_1210])).

cnf(c_4908,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3413,c_4904])).

cnf(c_5237,plain,
    ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5212,c_4908])).

cnf(c_3308,plain,
    ( k15_lattice3(sK9,k1_xboole_0) != X0
    | k5_lattices(sK9) != X0
    | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_5747,plain,
    ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0))
    | k5_lattices(sK9) != k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0))
    | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3308])).

cnf(c_5748,plain,
    ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0))
    | k5_lattices(sK9) != k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0))
    | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5747])).

cnf(c_6786,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_2545])).

cnf(c_2559,plain,
    ( X0 != X1
    | X2 != X3
    | k15_lattice3(X0,X2) = k15_lattice3(X1,X3) ),
    theory(equality)).

cnf(c_5848,plain,
    ( X0 != X1
    | k15_lattice3(sK9,X0) = k15_lattice3(X2,X1)
    | sK9 != X2 ),
    inference(instantiation,[status(thm)],[c_2559])).

cnf(c_7586,plain,
    ( X0 != X1
    | k15_lattice3(sK9,X0) = k15_lattice3(sK9,X1)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_5848])).

cnf(c_7587,plain,
    ( k15_lattice3(sK9,k1_xboole_0) = k15_lattice3(sK9,k1_xboole_0)
    | sK9 != sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7586])).

cnf(c_5132,plain,
    ( X0 != X1
    | k15_lattice3(sK9,X2) != X1
    | k15_lattice3(sK9,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_7544,plain,
    ( X0 != k15_lattice3(sK9,X1)
    | k15_lattice3(sK9,X1) = X0
    | k15_lattice3(sK9,X1) != k15_lattice3(sK9,X1) ),
    inference(instantiation,[status(thm)],[c_5132])).

cnf(c_11988,plain,
    ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) != k15_lattice3(sK9,k1_xboole_0)
    | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0))
    | k15_lattice3(sK9,k1_xboole_0) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7544])).

cnf(c_11989,plain,
    ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0)) != k15_lattice3(sK9,k1_xboole_0)
    | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0))
    | k15_lattice3(sK9,k1_xboole_0) != k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11988])).

cnf(c_12033,plain,
    ( v13_lattices(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9688,c_47,c_158,c_159,c_264,c_1210,c_3367,c_3806,c_4575,c_5237,c_5748,c_6786,c_7587,c_11989])).

cnf(c_15197,plain,
    ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),sK2(sK9,X0))) = sK2(sK9,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4528,c_47,c_158,c_159,c_264,c_1210,c_3367,c_3806,c_4575,c_5237,c_5748,c_6786,c_7587,c_11989])).

cnf(c_15198,plain,
    ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),sK2(sK9,X0))) = sK2(sK9,X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15197])).

cnf(c_15206,plain,
    ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),sK2(sK9,k15_lattice3(sK9,X0)))) = sK2(sK9,k15_lattice3(sK9,X0)) ),
    inference(superposition,[status(thm)],[c_3075,c_15198])).

cnf(c_3938,plain,
    ( k2_lattices(sK9,X0,k15_lattice3(sK9,X1)) = k2_lattices(sK9,k15_lattice3(sK9,X1),X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3075,c_3074])).

cnf(c_5339,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1)) = k2_lattices(sK9,k15_lattice3(sK9,X1),k15_lattice3(sK9,X0)) ),
    inference(superposition,[status(thm)],[c_3075,c_3938])).

cnf(c_5398,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5339,c_4904])).

cnf(c_15579,plain,
    ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,X0)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_15206,c_5398])).

cnf(c_15634,plain,
    ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_15579])).

cnf(c_4523,plain,
    ( k2_lattices(sK9,X0,sK2(sK9,X1)) = k2_lattices(sK9,sK2(sK9,X1),X0)
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3069,c_3074])).

cnf(c_14479,plain,
    ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | k2_lattices(sK9,X0,sK2(sK9,X1)) = k2_lattices(sK9,sK2(sK9,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4523,c_47,c_158,c_159,c_264,c_1210,c_3367,c_3806,c_4575,c_5237,c_5748,c_6786,c_7587,c_11989])).

cnf(c_14480,plain,
    ( k2_lattices(sK9,X0,sK2(sK9,X1)) = k2_lattices(sK9,sK2(sK9,X1),X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14479])).

cnf(c_14488,plain,
    ( k2_lattices(sK9,sK2(sK9,X0),k15_lattice3(sK9,X1)) = k2_lattices(sK9,k15_lattice3(sK9,X1),sK2(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3075,c_14480])).

cnf(c_14802,plain,
    ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,X0)),k15_lattice3(sK9,X1)) = k2_lattices(sK9,k15_lattice3(sK9,X1),sK2(sK9,k15_lattice3(sK9,X0))) ),
    inference(superposition,[status(thm)],[c_3075,c_14488])).

cnf(c_19,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_561,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(resolution,[status(thm)],[c_7,c_19])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_lattices(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_8])).

cnf(c_566,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(renaming,[status(thm)],[c_565])).

cnf(c_17,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_625,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_7,c_17])).

cnf(c_629,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_9,c_8])).

cnf(c_841,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(resolution,[status(thm)],[c_566,c_629])).

cnf(c_1135,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_841,c_45])).

cnf(c_1136,plain,
    ( r3_lattices(sK9,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k2_lattices(sK9,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_1135])).

cnf(c_1140,plain,
    ( r3_lattices(sK9,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1136,c_46,c_43])).

cnf(c_1141,plain,
    ( r3_lattices(sK9,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k2_lattices(sK9,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_1140])).

cnf(c_3077,plain,
    ( k2_lattices(sK9,X0,X1) != X0
    | r3_lattices(sK9,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1141])).

cnf(c_14930,plain,
    ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,X0)),k15_lattice3(sK9,X1)) != k15_lattice3(sK9,X1)
    | r3_lattices(sK9,k15_lattice3(sK9,X1),sK2(sK9,k15_lattice3(sK9,X0))) = iProver_top
    | m1_subset_1(k15_lattice3(sK9,X1),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9,k15_lattice3(sK9,X0)),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14802,c_3077])).

cnf(c_14954,plain,
    ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) != k15_lattice3(sK9,k1_xboole_0)
    | r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK2(sK9,k15_lattice3(sK9,k1_xboole_0))) = iProver_top
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14930])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,sK2(X1,X0)) != X0
    | k2_lattices(X1,sK2(X1,X0),X0) != X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1453,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v13_lattices(X1)
    | k2_lattices(X1,X0,sK2(X1,X0)) != X0
    | k2_lattices(X1,sK2(X1,X0),X0) != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_46])).

cnf(c_1454,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l1_lattices(sK9)
    | v13_lattices(sK9)
    | k2_lattices(sK9,X0,sK2(sK9,X0)) != X0
    | k2_lattices(sK9,sK2(sK9,X0),X0) != X0 ),
    inference(unflattening,[status(thm)],[c_1453])).

cnf(c_1458,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | v13_lattices(sK9)
    | k2_lattices(sK9,X0,sK2(sK9,X0)) != X0
    | k2_lattices(sK9,sK2(sK9,X0),X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1454,c_1222])).

cnf(c_3068,plain,
    ( k2_lattices(sK9,X0,sK2(sK9,X0)) != X0
    | k2_lattices(sK9,sK2(sK9,X0),X0) != X0
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_14929,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X0))) != k15_lattice3(sK9,X0)
    | m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_14802,c_3068])).

cnf(c_14951,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK2(sK9,k15_lattice3(sK9,k1_xboole_0))) != k15_lattice3(sK9,k1_xboole_0)
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14929])).

cnf(c_3225,plain,
    ( ~ r3_lattices(sK9,k15_lattice3(sK9,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
    | k2_lattices(sK9,k15_lattice3(sK9,X0),X1) = k15_lattice3(sK9,X0) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_3905,plain,
    ( ~ r3_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X1)))
    | ~ m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
    | ~ m1_subset_1(sK2(sK9,k15_lattice3(sK9,X1)),u1_struct_0(sK9))
    | k2_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X1))) = k15_lattice3(sK9,X0) ),
    inference(instantiation,[status(thm)],[c_3225])).

cnf(c_3911,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X1))) = k15_lattice3(sK9,X0)
    | r3_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X1))) != iProver_top
    | m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9,k15_lattice3(sK9,X1)),u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3905])).

cnf(c_3913,plain,
    ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK2(sK9,k15_lattice3(sK9,k1_xboole_0))) = k15_lattice3(sK9,k1_xboole_0)
    | r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK2(sK9,k15_lattice3(sK9,k1_xboole_0))) != iProver_top
    | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3911])).

cnf(c_3156,plain,
    ( ~ m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
    | m1_subset_1(sK2(sK9,k15_lattice3(sK9,X0)),u1_struct_0(sK9))
    | v13_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_3157,plain,
    ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9,k15_lattice3(sK9,X0)),u1_struct_0(sK9)) = iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3156])).

cnf(c_3159,plain,
    ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) = iProver_top
    | v13_lattices(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15634,c_14954,c_14951,c_12033,c_3913,c_3159,c_1210,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.75/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.50  
% 7.75/1.50  ------  iProver source info
% 7.75/1.50  
% 7.75/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.50  git: non_committed_changes: false
% 7.75/1.50  git: last_make_outside_of_git: false
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     num_symb
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       true
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  ------ Parsing...
% 7.75/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  ------ Proving...
% 7.75/1.50  ------ Problem Properties 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  clauses                                 32
% 7.75/1.50  conjectures                             1
% 7.75/1.50  EPR                                     0
% 7.75/1.50  Horn                                    26
% 7.75/1.50  unary                                   5
% 7.75/1.50  binary                                  13
% 7.75/1.50  lits                                    82
% 7.75/1.50  lits eq                                 24
% 7.75/1.50  fd_pure                                 0
% 7.75/1.50  fd_pseudo                               0
% 7.75/1.50  fd_cond                                 5
% 7.75/1.50  fd_pseudo_cond                          0
% 7.75/1.50  AC symbols                              0
% 7.75/1.50  
% 7.75/1.50  ------ Schedule dynamic 5 is on 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  Current options:
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     none
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       false
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS status Theorem for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  fof(f13,axiom,(
% 7.75/1.50    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f41,plain,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f13])).
% 7.75/1.50  
% 7.75/1.50  fof(f42,plain,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f110,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f42])).
% 7.75/1.50  
% 7.75/1.50  fof(f17,conjecture,(
% 7.75/1.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f18,negated_conjecture,(
% 7.75/1.50    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.75/1.50    inference(negated_conjecture,[],[f17])).
% 7.75/1.50  
% 7.75/1.50  fof(f49,plain,(
% 7.75/1.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f18])).
% 7.75/1.50  
% 7.75/1.50  fof(f50,plain,(
% 7.75/1.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f49])).
% 7.75/1.50  
% 7.75/1.50  fof(f78,plain,(
% 7.75/1.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) | ~l3_lattices(sK9) | ~v13_lattices(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f79,plain,(
% 7.75/1.50    (k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) | ~l3_lattices(sK9) | ~v13_lattices(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9)),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f50,f78])).
% 7.75/1.50  
% 7.75/1.50  fof(f125,plain,(
% 7.75/1.50    l3_lattices(sK9)),
% 7.75/1.50    inference(cnf_transformation,[],[f79])).
% 7.75/1.50  
% 7.75/1.50  fof(f122,plain,(
% 7.75/1.50    ~v2_struct_0(sK9)),
% 7.75/1.50    inference(cnf_transformation,[],[f79])).
% 7.75/1.50  
% 7.75/1.50  fof(f11,axiom,(
% 7.75/1.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f37,plain,(
% 7.75/1.50    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f11])).
% 7.75/1.50  
% 7.75/1.50  fof(f38,plain,(
% 7.75/1.50    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f37])).
% 7.75/1.50  
% 7.75/1.50  fof(f61,plain,(
% 7.75/1.50    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f38])).
% 7.75/1.50  
% 7.75/1.50  fof(f62,plain,(
% 7.75/1.50    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(rectify,[],[f61])).
% 7.75/1.50  
% 7.75/1.50  fof(f64,plain,(
% 7.75/1.50    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((k2_lattices(X0,X4,sK3(X0)) = sK3(X0) & k2_lattices(X0,sK3(X0),X4) = sK3(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f63,plain,(
% 7.75/1.50    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f65,plain,(
% 7.75/1.50    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((k2_lattices(X0,X4,sK3(X0)) = sK3(X0) & k2_lattices(X0,sK3(X0),X4) = sK3(X0)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f62,f64,f63])).
% 7.75/1.50  
% 7.75/1.50  fof(f104,plain,(
% 7.75/1.50    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f65])).
% 7.75/1.50  
% 7.75/1.50  fof(f8,axiom,(
% 7.75/1.50    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f20,plain,(
% 7.75/1.50    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 7.75/1.50    inference(pure_predicate_removal,[],[f8])).
% 7.75/1.50  
% 7.75/1.50  fof(f32,plain,(
% 7.75/1.50    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f20])).
% 7.75/1.50  
% 7.75/1.50  fof(f96,plain,(
% 7.75/1.50    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f32])).
% 7.75/1.50  
% 7.75/1.50  fof(f15,axiom,(
% 7.75/1.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f45,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f15])).
% 7.75/1.50  
% 7.75/1.50  fof(f46,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f45])).
% 7.75/1.50  
% 7.75/1.50  fof(f117,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f46])).
% 7.75/1.50  
% 7.75/1.50  fof(f124,plain,(
% 7.75/1.50    v4_lattice3(sK9)),
% 7.75/1.50    inference(cnf_transformation,[],[f79])).
% 7.75/1.50  
% 7.75/1.50  fof(f123,plain,(
% 7.75/1.50    v10_lattices(sK9)),
% 7.75/1.50    inference(cnf_transformation,[],[f79])).
% 7.75/1.50  
% 7.75/1.50  fof(f14,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f43,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 7.75/1.50    inference(ennf_transformation,[],[f14])).
% 7.75/1.50  
% 7.75/1.50  fof(f44,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 7.75/1.50    inference(flattening,[],[f43])).
% 7.75/1.50  
% 7.75/1.50  fof(f71,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 7.75/1.50    inference(nnf_transformation,[],[f44])).
% 7.75/1.50  
% 7.75/1.50  fof(f72,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 7.75/1.50    inference(rectify,[],[f71])).
% 7.75/1.50  
% 7.75/1.50  fof(f74,plain,(
% 7.75/1.50    ( ! [X5] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK7(X0,X1,X2),X2) & r3_lattices(X1,sK7(X0,X1,X2),X5) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f73,plain,(
% 7.75/1.50    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,sK6(X0,X1,X2)) & m1_subset_1(X6,u1_struct_0(X1))) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f75,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK7(X0,X1,X2),X2) & r3_lattices(X1,sK7(X0,X1,X2),sK6(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f72,f74,f73])).
% 7.75/1.50  
% 7.75/1.50  fof(f115,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f75])).
% 7.75/1.50  
% 7.75/1.50  fof(f113,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f75])).
% 7.75/1.50  
% 7.75/1.50  fof(f103,plain,(
% 7.75/1.50    ( ! [X4,X0] : (k2_lattices(X0,X4,sK3(X0)) = sK3(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f65])).
% 7.75/1.50  
% 7.75/1.50  fof(f3,axiom,(
% 7.75/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f53,plain,(
% 7.75/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.75/1.50    inference(nnf_transformation,[],[f3])).
% 7.75/1.50  
% 7.75/1.50  fof(f54,plain,(
% 7.75/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.75/1.50    inference(flattening,[],[f53])).
% 7.75/1.50  
% 7.75/1.50  fof(f83,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f54])).
% 7.75/1.50  
% 7.75/1.50  fof(f84,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.75/1.50    inference(cnf_transformation,[],[f54])).
% 7.75/1.50  
% 7.75/1.50  fof(f128,plain,(
% 7.75/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.75/1.50    inference(equality_resolution,[],[f84])).
% 7.75/1.50  
% 7.75/1.50  fof(f126,plain,(
% 7.75/1.50    k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) | ~l3_lattices(sK9) | ~v13_lattices(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)),
% 7.75/1.50    inference(cnf_transformation,[],[f79])).
% 7.75/1.50  
% 7.75/1.50  fof(f6,axiom,(
% 7.75/1.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f28,plain,(
% 7.75/1.50    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f6])).
% 7.75/1.50  
% 7.75/1.50  fof(f29,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f28])).
% 7.75/1.50  
% 7.75/1.50  fof(f55,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f29])).
% 7.75/1.50  
% 7.75/1.50  fof(f56,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(rectify,[],[f55])).
% 7.75/1.50  
% 7.75/1.50  fof(f57,plain,(
% 7.75/1.50    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f58,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).
% 7.75/1.50  
% 7.75/1.50  fof(f91,plain,(
% 7.75/1.50    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f58])).
% 7.75/1.50  
% 7.75/1.50  fof(f130,plain,(
% 7.75/1.50    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(equality_resolution,[],[f91])).
% 7.75/1.50  
% 7.75/1.50  fof(f7,axiom,(
% 7.75/1.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f30,plain,(
% 7.75/1.50    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f7])).
% 7.75/1.50  
% 7.75/1.50  fof(f31,plain,(
% 7.75/1.50    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f30])).
% 7.75/1.50  
% 7.75/1.50  fof(f95,plain,(
% 7.75/1.50    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f31])).
% 7.75/1.50  
% 7.75/1.50  fof(f12,axiom,(
% 7.75/1.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f39,plain,(
% 7.75/1.50    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f12])).
% 7.75/1.50  
% 7.75/1.50  fof(f40,plain,(
% 7.75/1.50    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f39])).
% 7.75/1.50  
% 7.75/1.50  fof(f66,plain,(
% 7.75/1.50    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f67,plain,(
% 7.75/1.50    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(rectify,[],[f66])).
% 7.75/1.50  
% 7.75/1.50  fof(f69,plain,(
% 7.75/1.50    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,sK5(X0)) != k2_lattices(X0,sK5(X0),X1) & m1_subset_1(sK5(X0),u1_struct_0(X0))))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f68,plain,(
% 7.75/1.50    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,X2,sK4(X0)) != k2_lattices(X0,sK4(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f70,plain,(
% 7.75/1.50    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f67,f69,f68])).
% 7.75/1.50  
% 7.75/1.50  fof(f106,plain,(
% 7.75/1.50    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f70])).
% 7.75/1.50  
% 7.75/1.50  fof(f5,axiom,(
% 7.75/1.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f21,plain,(
% 7.75/1.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.75/1.50    inference(pure_predicate_removal,[],[f5])).
% 7.75/1.50  
% 7.75/1.50  fof(f22,plain,(
% 7.75/1.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.75/1.50    inference(pure_predicate_removal,[],[f21])).
% 7.75/1.50  
% 7.75/1.50  fof(f23,plain,(
% 7.75/1.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 7.75/1.50    inference(pure_predicate_removal,[],[f22])).
% 7.75/1.50  
% 7.75/1.50  fof(f26,plain,(
% 7.75/1.50    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f23])).
% 7.75/1.50  
% 7.75/1.50  fof(f27,plain,(
% 7.75/1.50    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 7.75/1.50    inference(flattening,[],[f26])).
% 7.75/1.50  
% 7.75/1.50  fof(f88,plain,(
% 7.75/1.50    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f16,axiom,(
% 7.75/1.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f47,plain,(
% 7.75/1.50    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f16])).
% 7.75/1.50  
% 7.75/1.50  fof(f48,plain,(
% 7.75/1.50    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f47])).
% 7.75/1.50  
% 7.75/1.50  fof(f76,plain,(
% 7.75/1.50    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK8(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f77,plain,(
% 7.75/1.50    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK8(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f76])).
% 7.75/1.50  
% 7.75/1.50  fof(f120,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | r2_hidden(sK8(X0,X1,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f77])).
% 7.75/1.50  
% 7.75/1.50  fof(f85,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.75/1.50    inference(cnf_transformation,[],[f54])).
% 7.75/1.50  
% 7.75/1.50  fof(f127,plain,(
% 7.75/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.75/1.50    inference(equality_resolution,[],[f85])).
% 7.75/1.50  
% 7.75/1.50  fof(f4,axiom,(
% 7.75/1.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f86,plain,(
% 7.75/1.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f4])).
% 7.75/1.50  
% 7.75/1.50  fof(f90,plain,(
% 7.75/1.50    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f9,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f33,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f9])).
% 7.75/1.50  
% 7.75/1.50  fof(f34,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f33])).
% 7.75/1.50  
% 7.75/1.50  fof(f59,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f34])).
% 7.75/1.50  
% 7.75/1.50  fof(f97,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f59])).
% 7.75/1.50  
% 7.75/1.50  fof(f89,plain,(
% 7.75/1.50    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f10,axiom,(
% 7.75/1.50    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f35,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f10])).
% 7.75/1.50  
% 7.75/1.50  fof(f36,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f35])).
% 7.75/1.50  
% 7.75/1.50  fof(f60,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f36])).
% 7.75/1.50  
% 7.75/1.50  fof(f99,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f100,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f98,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f59])).
% 7.75/1.50  
% 7.75/1.50  fof(f105,plain,(
% 7.75/1.50    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f65])).
% 7.75/1.50  
% 7.75/1.50  cnf(c_30,plain,
% 7.75/1.50      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 7.75/1.50      | ~ l3_lattices(X0)
% 7.75/1.50      | v2_struct_0(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f110]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_43,negated_conjecture,
% 7.75/1.50      ( l3_lattices(sK9) ),
% 7.75/1.50      inference(cnf_transformation,[],[f125]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1206,plain,
% 7.75/1.50      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 7.75/1.50      | v2_struct_0(X0)
% 7.75/1.50      | sK9 != X0 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_30,c_43]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1207,plain,
% 7.75/1.50      ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
% 7.75/1.50      | v2_struct_0(sK9) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_1206]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_46,negated_conjecture,
% 7.75/1.50      ( ~ v2_struct_0(sK9) ),
% 7.75/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1211,plain,
% 7.75/1.50      ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_1207,c_46]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3075,plain,
% 7.75/1.50      ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1211]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.50      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 7.75/1.50      | ~ l1_lattices(X1)
% 7.75/1.50      | v13_lattices(X1)
% 7.75/1.50      | v2_struct_0(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1432,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.50      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 7.75/1.50      | ~ l1_lattices(X1)
% 7.75/1.50      | v13_lattices(X1)
% 7.75/1.50      | sK9 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_46]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1433,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.50      | m1_subset_1(sK2(sK9,X0),u1_struct_0(sK9))
% 7.75/1.50      | ~ l1_lattices(sK9)
% 7.75/1.50      | v13_lattices(sK9) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_1432]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_16,plain,
% 7.75/1.50      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1221,plain,
% 7.75/1.50      ( l1_lattices(X0) | sK9 != X0 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_43]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1222,plain,
% 7.75/1.50      ( l1_lattices(sK9) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_1221]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1437,plain,
% 7.75/1.50      ( m1_subset_1(sK2(sK9,X0),u1_struct_0(sK9))
% 7.75/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.50      | v13_lattices(sK9) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_1433,c_1222]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1438,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.50      | m1_subset_1(sK2(sK9,X0),u1_struct_0(sK9))
% 7.75/1.50      | v13_lattices(sK9) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_1437]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3069,plain,
% 7.75/1.50      ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.50      | m1_subset_1(sK2(sK9,X0),u1_struct_0(sK9)) = iProver_top
% 7.75/1.50      | v13_lattices(sK9) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1438]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_38,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.50      | ~ v4_lattice3(X1)
% 7.75/1.50      | ~ l3_lattices(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | ~ v10_lattices(X1)
% 7.75/1.50      | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_44,negated_conjecture,
% 7.75/1.50      ( v4_lattice3(sK9) ),
% 7.75/1.50      inference(cnf_transformation,[],[f124]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_884,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.50      | ~ l3_lattices(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | ~ v10_lattices(X1)
% 7.75/1.50      | k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0
% 7.75/1.50      | sK9 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_38,c_44]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_885,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.50      | ~ l3_lattices(sK9)
% 7.75/1.50      | v2_struct_0(sK9)
% 7.75/1.50      | ~ v10_lattices(sK9)
% 7.75/1.50      | k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),X0)) = X0 ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_884]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_45,negated_conjecture,
% 7.75/1.50      ( v10_lattices(sK9) ),
% 7.75/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_889,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.50      | k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),X0)) = X0 ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_885,c_46,c_45,c_43]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3088,plain,
% 7.75/1.50      ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),X0)) = X0
% 7.75/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_889]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4528,plain,
% 7.75/1.50      ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),sK2(sK9,X0))) = sK2(sK9,X0)
% 7.75/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.50      | v13_lattices(sK9) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3069,c_3088]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_32,plain,
% 7.75/1.50      ( ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
% 7.75/1.50      | r2_hidden(sK7(X0,X1,X2),X2)
% 7.75/1.50      | ~ v4_lattice3(X1)
% 7.75/1.50      | ~ l3_lattices(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | ~ v10_lattices(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f115]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_974,plain,
% 7.75/1.50      ( ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
% 7.75/1.50      | r2_hidden(sK7(X0,X1,X2),X2)
% 7.75/1.50      | ~ l3_lattices(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | ~ v10_lattices(X1)
% 7.75/1.50      | sK9 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_32,c_44]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_975,plain,
% 7.75/1.50      ( ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1))
% 7.75/1.50      | r2_hidden(sK7(X0,sK9,X1),X1)
% 7.75/1.50      | ~ l3_lattices(sK9)
% 7.75/1.50      | v2_struct_0(sK9)
% 7.75/1.50      | ~ v10_lattices(sK9) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_974]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_979,plain,
% 7.75/1.50      ( r2_hidden(sK7(X0,sK9,X1),X1)
% 7.75/1.50      | ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1)) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_975,c_46,c_45,c_43]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_980,plain,
% 7.75/1.50      ( ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1))
% 7.75/1.50      | r2_hidden(sK7(X0,sK9,X1),X1) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_979]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3083,plain,
% 7.75/1.50      ( r2_hidden(X0,a_2_6_lattice3(sK9,X1)) != iProver_top
% 7.75/1.50      | r2_hidden(sK7(X0,sK9,X1),X1) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_34,plain,
% 7.75/1.50      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
% 7.75/1.50      | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
% 7.75/1.50      | ~ v4_lattice3(X1)
% 7.75/1.50      | ~ l3_lattices(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | ~ v10_lattices(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_956,plain,
% 7.75/1.50      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
% 7.75/1.50      | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
% 7.75/1.50      | ~ l3_lattices(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | ~ v10_lattices(X1)
% 7.75/1.50      | sK9 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_34,c_44]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_957,plain,
% 7.75/1.50      ( m1_subset_1(sK7(X0,sK9,X1),u1_struct_0(sK9))
% 7.75/1.50      | ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1))
% 7.75/1.50      | ~ l3_lattices(sK9)
% 7.75/1.50      | v2_struct_0(sK9)
% 7.75/1.50      | ~ v10_lattices(sK9) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_956]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_961,plain,
% 7.75/1.50      ( ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1))
% 7.75/1.50      | m1_subset_1(sK7(X0,sK9,X1),u1_struct_0(sK9)) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_957,c_46,c_45,c_43]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_962,plain,
% 7.75/1.50      ( m1_subset_1(sK7(X0,sK9,X1),u1_struct_0(sK9))
% 7.75/1.50      | ~ r2_hidden(X0,a_2_6_lattice3(sK9,X1)) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_961]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3084,plain,
% 7.75/1.50      ( m1_subset_1(sK7(X0,sK9,X1),u1_struct_0(sK9)) = iProver_top
% 7.75/1.50      | r2_hidden(X0,a_2_6_lattice3(sK9,X1)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.50      | ~ l1_lattices(X1)
% 7.75/1.50      | ~ v13_lattices(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | k2_lattices(X1,X0,sK3(X1)) = sK3(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1411,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.50      | ~ l1_lattices(X1)
% 7.75/1.50      | ~ v13_lattices(X1)
% 7.75/1.50      | k2_lattices(X1,X0,sK3(X1)) = sK3(X1)
% 7.75/1.50      | sK9 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_23,c_46]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1412,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.50      | ~ l1_lattices(sK9)
% 7.75/1.50      | ~ v13_lattices(sK9)
% 7.75/1.50      | k2_lattices(sK9,X0,sK3(sK9)) = sK3(sK9) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_1411]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1416,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.50      | ~ v13_lattices(sK9)
% 7.75/1.50      | k2_lattices(sK9,X0,sK3(sK9)) = sK3(sK9) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_1412,c_1222]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3070,plain,
% 7.75/1.50      ( k2_lattices(sK9,X0,sK3(sK9)) = sK3(sK9)
% 7.75/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.50      | v13_lattices(sK9) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1416]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3782,plain,
% 7.75/1.50      ( k2_lattices(sK9,sK7(X0,sK9,X1),sK3(sK9)) = sK3(sK9)
% 7.75/1.50      | r2_hidden(X0,a_2_6_lattice3(sK9,X1)) != iProver_top
% 7.75/1.50      | v13_lattices(sK9) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3084,c_3070]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5887,plain,
% 7.75/1.50      ( k2_lattices(sK9,sK7(sK7(X0,sK9,a_2_6_lattice3(sK9,X1)),sK9,X1),sK3(sK9)) = sK3(sK9)
% 7.75/1.50      | r2_hidden(X0,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))) != iProver_top
% 7.75/1.50      | v13_lattices(sK9) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3083,c_3782]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6346,plain,
% 7.75/1.50      ( k2_lattices(sK9,sK7(sK7(sK7(X0,sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))),sK9,a_2_6_lattice3(sK9,X1)),sK9,X1),sK3(sK9)) = sK3(sK9)
% 7.75/1.50      | r2_hidden(X0,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1)))) != iProver_top
% 7.75/1.50      | v13_lattices(sK9) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3083,c_5887]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7183,plain,
% 7.75/1.50      ( k2_lattices(sK9,sK7(sK7(sK7(sK7(X0,sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1)))),sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))),sK9,a_2_6_lattice3(sK9,X1)),sK9,X1),sK3(sK9)) = sK3(sK9)
% 7.75/1.50      | r2_hidden(X0,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))))) != iProver_top
% 7.75/1.50      | v13_lattices(sK9) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3083,c_6346]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_9688,plain,
% 7.75/1.50      ( k2_lattices(sK9,sK7(sK7(sK7(sK7(sK7(X0,sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))))),sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1)))),sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1))),sK9,a_2_6_lattice3(sK9,X1)),sK9,X1),sK3(sK9)) = sK3(sK9)
% 7.75/1.50      | r2_hidden(X0,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,a_2_6_lattice3(sK9,X1)))))) != iProver_top
% 7.75/1.50      | v13_lattices(sK9) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3083,c_7183]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_47,plain,
% 7.75/1.50      ( v2_struct_0(sK9) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5,plain,
% 7.75/1.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.75/1.50      | k1_xboole_0 = X0
% 7.75/1.50      | k1_xboole_0 = X1 ),
% 7.75/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_158,plain,
% 7.75/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.75/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4,plain,
% 7.75/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f128]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_159,plain,
% 7.75/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_42,negated_conjecture,
% 7.75/1.50      ( ~ v13_lattices(sK9)
% 7.75/1.50      | ~ l3_lattices(sK9)
% 7.75/1.50      | v2_struct_0(sK9)
% 7.75/1.50      | ~ v10_lattices(sK9)
% 7.75/1.50      | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f126]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_262,negated_conjecture,
% 7.75/1.50      ( ~ v13_lattices(sK9)
% 7.75/1.50      | k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_42,c_46,c_45,c_43]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_264,plain,
% 7.75/1.50      ( k5_lattices(sK9) != k15_lattice3(sK9,k1_xboole_0)
% 7.75/1.50      | v13_lattices(sK9) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1208,plain,
% 7.75/1.50      ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) = iProver_top
% 7.75/1.50      | v2_struct_0(sK9) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1210,plain,
% 7.75/1.50      ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) = iProver_top
% 7.75/1.50      | v2_struct_0(sK9) = iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1208]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.50      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 7.75/1.50      | ~ l1_lattices(X1)
% 7.75/1.50      | ~ v13_lattices(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f130]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1477,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.50      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 7.75/1.50      | ~ l1_lattices(X1)
% 7.75/1.50      | ~ v13_lattices(X1)
% 7.75/1.50      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
% 7.75/1.50      | sK9 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_14,c_46]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1478,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.50      | ~ m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 7.75/1.50      | ~ l1_lattices(sK9)
% 7.75/1.50      | ~ v13_lattices(sK9)
% 7.75/1.50      | k2_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_1477]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_15,plain,
% 7.75/1.50      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 7.75/1.50      | ~ l1_lattices(X0)
% 7.75/1.50      | v2_struct_0(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1360,plain,
% 7.75/1.50      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 7.75/1.50      | ~ l1_lattices(X0)
% 7.75/1.50      | sK9 != X0 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_15,c_46]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1361,plain,
% 7.75/1.50      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 7.75/1.50      | ~ l1_lattices(sK9) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_1360]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1482,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.50      | ~ v13_lattices(sK9)
% 7.75/1.50      | k2_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_1478,c_1222,c_1361]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3364,plain,
% 7.75/1.50      ( ~ m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
% 7.75/1.50      | ~ v13_lattices(sK9)
% 7.75/1.50      | k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) = k5_lattices(sK9) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1482]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3365,plain,
% 7.75/1.50      ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) = k5_lattices(sK9)
% 7.75/1.50      | m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.50      | v13_lattices(sK9) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_3364]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3367,plain,
% 7.75/1.50      ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0)) = k5_lattices(sK9)
% 7.75/1.50      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.50      | v13_lattices(sK9) != iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_3365]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2545,plain,( X0 = X0 ),theory(equality) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3806,plain,
% 7.75/1.50      ( k5_lattices(sK9) = k5_lattices(sK9) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_2545]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2546,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3569,plain,
% 7.75/1.50      ( X0 != X1 | k5_lattices(sK9) != X1 | k5_lattices(sK9) = X0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_2546]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4027,plain,
% 7.75/1.50      ( X0 != k5_lattices(sK9)
% 7.75/1.50      | k5_lattices(sK9) = X0
% 7.75/1.50      | k5_lattices(sK9) != k5_lattices(sK9) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_3569]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4574,plain,
% 7.75/1.51      ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) != k5_lattices(sK9)
% 7.75/1.51      | k5_lattices(sK9) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0))
% 7.75/1.51      | k5_lattices(sK9) != k5_lattices(sK9) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_4027]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4575,plain,
% 7.75/1.51      ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0)) != k5_lattices(sK9)
% 7.75/1.51      | k5_lattices(sK9) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0))
% 7.75/1.51      | k5_lattices(sK9) != k5_lattices(sK9) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_4574]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1363,plain,
% 7.75/1.51      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1361,c_1222]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3072,plain,
% 7.75/1.51      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1363]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_29,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.75/1.51      | ~ l1_lattices(X1)
% 7.75/1.51      | ~ v6_lattices(X1)
% 7.75/1.51      | v2_struct_0(X1)
% 7.75/1.51      | k2_lattices(X1,X2,X0) = k2_lattices(X1,X0,X2) ),
% 7.75/1.51      inference(cnf_transformation,[],[f106]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1371,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.75/1.51      | ~ l1_lattices(X1)
% 7.75/1.51      | ~ v6_lattices(X1)
% 7.75/1.51      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 7.75/1.51      | sK9 != X1 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_29,c_46]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1372,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | ~ l1_lattices(sK9)
% 7.75/1.51      | ~ v6_lattices(sK9)
% 7.75/1.51      | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_1371]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_9,plain,
% 7.75/1.51      ( v6_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1183,plain,
% 7.75/1.51      ( v6_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | sK9 != X0 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_9,c_45]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1184,plain,
% 7.75/1.51      ( v6_lattices(sK9) | ~ l3_lattices(sK9) | v2_struct_0(sK9) ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_1183]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1186,plain,
% 7.75/1.51      ( v6_lattices(sK9) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1184,c_46,c_43]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1298,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.75/1.51      | ~ l1_lattices(X1)
% 7.75/1.51      | v2_struct_0(X1)
% 7.75/1.51      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
% 7.75/1.51      | sK9 != X1 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_29,c_1186]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1299,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | ~ l1_lattices(sK9)
% 7.75/1.51      | v2_struct_0(sK9)
% 7.75/1.51      | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_1298]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1303,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1299,c_46,c_1222]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1376,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1372,c_46,c_1222,c_1299]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3074,plain,
% 7.75/1.51      ( k2_lattices(sK9,X0,X1) = k2_lattices(sK9,X1,X0)
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1376]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3940,plain,
% 7.75/1.51      ( k2_lattices(sK9,X0,k5_lattices(sK9)) = k2_lattices(sK9,k5_lattices(sK9),X0)
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3072,c_3074]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5212,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,X0),k5_lattices(sK9)) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3075,c_3940]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3413,plain,
% 7.75/1.51      ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),k5_lattices(sK9))) = k5_lattices(sK9) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3072,c_3088]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_40,plain,
% 7.75/1.51      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 7.75/1.51      | r2_hidden(sK8(X0,X1,X2),X1)
% 7.75/1.51      | ~ v4_lattice3(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f120]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1010,plain,
% 7.75/1.51      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
% 7.75/1.51      | r2_hidden(sK8(X0,X1,X2),X1)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | sK9 != X0 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_40,c_44]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1011,plain,
% 7.75/1.51      ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1))
% 7.75/1.51      | r2_hidden(sK8(sK9,X0,X1),X0)
% 7.75/1.51      | ~ l3_lattices(sK9)
% 7.75/1.51      | v2_struct_0(sK9)
% 7.75/1.51      | ~ v10_lattices(sK9) ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_1010]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1015,plain,
% 7.75/1.51      ( r2_hidden(sK8(sK9,X0,X1),X0)
% 7.75/1.51      | r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1)) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1011,c_46,c_45,c_43]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1016,plain,
% 7.75/1.51      ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1))
% 7.75/1.51      | r2_hidden(sK8(sK9,X0,X1),X0) ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_1015]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3081,plain,
% 7.75/1.51      ( r3_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1)) = iProver_top
% 7.75/1.51      | r2_hidden(sK8(sK9,X0,X1),X0) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3,plain,
% 7.75/1.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.75/1.51      inference(cnf_transformation,[],[f127]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6,plain,
% 7.75/1.51      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 7.75/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3092,plain,
% 7.75/1.51      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4062,plain,
% 7.75/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3,c_3092]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4464,plain,
% 7.75/1.51      ( r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0)) = iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3081,c_4062]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7,plain,
% 7.75/1.51      ( ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | v9_lattices(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_18,plain,
% 7.75/1.51      ( r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ v6_lattices(X0)
% 7.75/1.51      | ~ v8_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v9_lattices(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_593,plain,
% 7.75/1.51      ( r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ v6_lattices(X0)
% 7.75/1.51      | ~ v8_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0) ),
% 7.75/1.51      inference(resolution,[status(thm)],[c_7,c_18]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_8,plain,
% 7.75/1.51      ( v8_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_597,plain,
% 7.75/1.51      ( r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_593,c_9,c_8]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_20,plain,
% 7.75/1.51      ( ~ r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ v8_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v9_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) = X1 ),
% 7.75/1.51      inference(cnf_transformation,[],[f99]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_529,plain,
% 7.75/1.51      ( ~ r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ v8_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) = X1 ),
% 7.75/1.51      inference(resolution,[status(thm)],[c_7,c_20]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_533,plain,
% 7.75/1.51      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) = X1 ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_529,c_8]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_534,plain,
% 7.75/1.51      ( ~ r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) = X1 ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_533]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_815,plain,
% 7.75/1.51      ( ~ r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) = X1 ),
% 7.75/1.51      inference(resolution,[status(thm)],[c_597,c_534]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1159,plain,
% 7.75/1.51      ( ~ r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) = X1
% 7.75/1.51      | sK9 != X0 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_815,c_45]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1160,plain,
% 7.75/1.51      ( ~ r3_lattices(sK9,X0,X1)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | ~ l3_lattices(sK9)
% 7.75/1.51      | v2_struct_0(sK9)
% 7.75/1.51      | k2_lattices(sK9,X0,X1) = X0 ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_1159]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1164,plain,
% 7.75/1.51      ( ~ r3_lattices(sK9,X0,X1)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | k2_lattices(sK9,X0,X1) = X0 ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1160,c_46,c_43]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1165,plain,
% 7.75/1.51      ( ~ r3_lattices(sK9,X0,X1)
% 7.75/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | k2_lattices(sK9,X0,X1) = X0 ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_1164]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3076,plain,
% 7.75/1.51      ( k2_lattices(sK9,X0,X1) = X0
% 7.75/1.51      | r3_lattices(sK9,X0,X1) != iProver_top
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4542,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0)) = k15_lattice3(sK9,k1_xboole_0)
% 7.75/1.51      | m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_4464,c_3076]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4904,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k15_lattice3(sK9,X0)) = k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_4542,c_47,c_1208,c_1210]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4908,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),k5_lattices(sK9)) = k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3413,c_4904]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5237,plain,
% 7.75/1.51      ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_5212,c_4908]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3308,plain,
% 7.75/1.51      ( k15_lattice3(sK9,k1_xboole_0) != X0
% 7.75/1.51      | k5_lattices(sK9) != X0
% 7.75/1.51      | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2546]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5747,plain,
% 7.75/1.51      ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0))
% 7.75/1.51      | k5_lattices(sK9) != k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0))
% 7.75/1.51      | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_3308]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5748,plain,
% 7.75/1.51      ( k15_lattice3(sK9,k1_xboole_0) != k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0))
% 7.75/1.51      | k5_lattices(sK9) != k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0))
% 7.75/1.51      | k5_lattices(sK9) = k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_5747]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6786,plain,
% 7.75/1.51      ( sK9 = sK9 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2545]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2559,plain,
% 7.75/1.51      ( X0 != X1 | X2 != X3 | k15_lattice3(X0,X2) = k15_lattice3(X1,X3) ),
% 7.75/1.51      theory(equality) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5848,plain,
% 7.75/1.51      ( X0 != X1
% 7.75/1.51      | k15_lattice3(sK9,X0) = k15_lattice3(X2,X1)
% 7.75/1.51      | sK9 != X2 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2559]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7586,plain,
% 7.75/1.51      ( X0 != X1
% 7.75/1.51      | k15_lattice3(sK9,X0) = k15_lattice3(sK9,X1)
% 7.75/1.51      | sK9 != sK9 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_5848]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7587,plain,
% 7.75/1.51      ( k15_lattice3(sK9,k1_xboole_0) = k15_lattice3(sK9,k1_xboole_0)
% 7.75/1.51      | sK9 != sK9
% 7.75/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_7586]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5132,plain,
% 7.75/1.51      ( X0 != X1
% 7.75/1.51      | k15_lattice3(sK9,X2) != X1
% 7.75/1.51      | k15_lattice3(sK9,X2) = X0 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2546]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7544,plain,
% 7.75/1.51      ( X0 != k15_lattice3(sK9,X1)
% 7.75/1.51      | k15_lattice3(sK9,X1) = X0
% 7.75/1.51      | k15_lattice3(sK9,X1) != k15_lattice3(sK9,X1) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_5132]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_11988,plain,
% 7.75/1.51      ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0)) != k15_lattice3(sK9,k1_xboole_0)
% 7.75/1.51      | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,X0))
% 7.75/1.51      | k15_lattice3(sK9,k1_xboole_0) != k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_7544]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_11989,plain,
% 7.75/1.51      ( k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0)) != k15_lattice3(sK9,k1_xboole_0)
% 7.75/1.51      | k15_lattice3(sK9,k1_xboole_0) = k2_lattices(sK9,k5_lattices(sK9),k15_lattice3(sK9,k1_xboole_0))
% 7.75/1.51      | k15_lattice3(sK9,k1_xboole_0) != k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_11988]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_12033,plain,
% 7.75/1.51      ( v13_lattices(sK9) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_9688,c_47,c_158,c_159,c_264,c_1210,c_3367,c_3806,
% 7.75/1.51                 c_4575,c_5237,c_5748,c_6786,c_7587,c_11989]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_15197,plain,
% 7.75/1.51      ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),sK2(sK9,X0))) = sK2(sK9,X0) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_4528,c_47,c_158,c_159,c_264,c_1210,c_3367,c_3806,
% 7.75/1.51                 c_4575,c_5237,c_5748,c_6786,c_7587,c_11989]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_15198,plain,
% 7.75/1.51      ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),sK2(sK9,X0))) = sK2(sK9,X0)
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_15197]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_15206,plain,
% 7.75/1.51      ( k15_lattice3(sK9,k6_domain_1(u1_struct_0(sK9),sK2(sK9,k15_lattice3(sK9,X0)))) = sK2(sK9,k15_lattice3(sK9,X0)) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3075,c_15198]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3938,plain,
% 7.75/1.51      ( k2_lattices(sK9,X0,k15_lattice3(sK9,X1)) = k2_lattices(sK9,k15_lattice3(sK9,X1),X0)
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3075,c_3074]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5339,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,X1)) = k2_lattices(sK9,k15_lattice3(sK9,X1),k15_lattice3(sK9,X0)) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3075,c_3938]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5398,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,X0),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_5339,c_4904]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_15579,plain,
% 7.75/1.51      ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,X0)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_15206,c_5398]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_15634,plain,
% 7.75/1.51      ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) = k15_lattice3(sK9,k1_xboole_0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_15579]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4523,plain,
% 7.75/1.51      ( k2_lattices(sK9,X0,sK2(sK9,X1)) = k2_lattices(sK9,sK2(sK9,X1),X0)
% 7.75/1.51      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | v13_lattices(sK9) = iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3069,c_3074]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14479,plain,
% 7.75/1.51      ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | k2_lattices(sK9,X0,sK2(sK9,X1)) = k2_lattices(sK9,sK2(sK9,X1),X0) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_4523,c_47,c_158,c_159,c_264,c_1210,c_3367,c_3806,
% 7.75/1.51                 c_4575,c_5237,c_5748,c_6786,c_7587,c_11989]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14480,plain,
% 7.75/1.51      ( k2_lattices(sK9,X0,sK2(sK9,X1)) = k2_lattices(sK9,sK2(sK9,X1),X0)
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_14479]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14488,plain,
% 7.75/1.51      ( k2_lattices(sK9,sK2(sK9,X0),k15_lattice3(sK9,X1)) = k2_lattices(sK9,k15_lattice3(sK9,X1),sK2(sK9,X0))
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3075,c_14480]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14802,plain,
% 7.75/1.51      ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,X0)),k15_lattice3(sK9,X1)) = k2_lattices(sK9,k15_lattice3(sK9,X1),sK2(sK9,k15_lattice3(sK9,X0))) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3075,c_14488]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_19,plain,
% 7.75/1.51      ( r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ v8_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v9_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) != X1 ),
% 7.75/1.51      inference(cnf_transformation,[],[f100]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_561,plain,
% 7.75/1.51      ( r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ v8_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) != X1 ),
% 7.75/1.51      inference(resolution,[status(thm)],[c_7,c_19]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_565,plain,
% 7.75/1.51      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) != X1 ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_561,c_8]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_566,plain,
% 7.75/1.51      ( r1_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) != X1 ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_565]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_17,plain,
% 7.75/1.51      ( ~ r1_lattices(X0,X1,X2)
% 7.75/1.51      | r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ v6_lattices(X0)
% 7.75/1.51      | ~ v8_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v9_lattices(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_625,plain,
% 7.75/1.51      ( ~ r1_lattices(X0,X1,X2)
% 7.75/1.51      | r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ v6_lattices(X0)
% 7.75/1.51      | ~ v8_lattices(X0)
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0) ),
% 7.75/1.51      inference(resolution,[status(thm)],[c_7,c_17]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_629,plain,
% 7.75/1.51      ( ~ r1_lattices(X0,X1,X2)
% 7.75/1.51      | r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_625,c_9,c_8]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_841,plain,
% 7.75/1.51      ( r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | ~ v10_lattices(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) != X1 ),
% 7.75/1.51      inference(resolution,[status(thm)],[c_566,c_629]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1135,plain,
% 7.75/1.51      ( r3_lattices(X0,X1,X2)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.75/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.51      | ~ l3_lattices(X0)
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | k2_lattices(X0,X1,X2) != X1
% 7.75/1.51      | sK9 != X0 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_841,c_45]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1136,plain,
% 7.75/1.51      ( r3_lattices(sK9,X0,X1)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | ~ l3_lattices(sK9)
% 7.75/1.51      | v2_struct_0(sK9)
% 7.75/1.51      | k2_lattices(sK9,X0,X1) != X0 ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_1135]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1140,plain,
% 7.75/1.51      ( r3_lattices(sK9,X0,X1)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | k2_lattices(sK9,X0,X1) != X0 ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1136,c_46,c_43]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1141,plain,
% 7.75/1.51      ( r3_lattices(sK9,X0,X1)
% 7.75/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | k2_lattices(sK9,X0,X1) != X0 ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_1140]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3077,plain,
% 7.75/1.51      ( k2_lattices(sK9,X0,X1) != X0
% 7.75/1.51      | r3_lattices(sK9,X0,X1) = iProver_top
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1141]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14930,plain,
% 7.75/1.51      ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,X0)),k15_lattice3(sK9,X1)) != k15_lattice3(sK9,X1)
% 7.75/1.51      | r3_lattices(sK9,k15_lattice3(sK9,X1),sK2(sK9,k15_lattice3(sK9,X0))) = iProver_top
% 7.75/1.51      | m1_subset_1(k15_lattice3(sK9,X1),u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(sK2(sK9,k15_lattice3(sK9,X0)),u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_14802,c_3077]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14954,plain,
% 7.75/1.51      ( k2_lattices(sK9,sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),k15_lattice3(sK9,k1_xboole_0)) != k15_lattice3(sK9,k1_xboole_0)
% 7.75/1.51      | r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK2(sK9,k15_lattice3(sK9,k1_xboole_0))) = iProver_top
% 7.75/1.51      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_14930]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_21,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.51      | ~ l1_lattices(X1)
% 7.75/1.51      | v13_lattices(X1)
% 7.75/1.51      | v2_struct_0(X1)
% 7.75/1.51      | k2_lattices(X1,X0,sK2(X1,X0)) != X0
% 7.75/1.51      | k2_lattices(X1,sK2(X1,X0),X0) != X0 ),
% 7.75/1.51      inference(cnf_transformation,[],[f105]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1453,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.75/1.51      | ~ l1_lattices(X1)
% 7.75/1.51      | v13_lattices(X1)
% 7.75/1.51      | k2_lattices(X1,X0,sK2(X1,X0)) != X0
% 7.75/1.51      | k2_lattices(X1,sK2(X1,X0),X0) != X0
% 7.75/1.51      | sK9 != X1 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_21,c_46]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1454,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | ~ l1_lattices(sK9)
% 7.75/1.51      | v13_lattices(sK9)
% 7.75/1.51      | k2_lattices(sK9,X0,sK2(sK9,X0)) != X0
% 7.75/1.51      | k2_lattices(sK9,sK2(sK9,X0),X0) != X0 ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_1453]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1458,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 7.75/1.51      | v13_lattices(sK9)
% 7.75/1.51      | k2_lattices(sK9,X0,sK2(sK9,X0)) != X0
% 7.75/1.51      | k2_lattices(sK9,sK2(sK9,X0),X0) != X0 ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1454,c_1222]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3068,plain,
% 7.75/1.51      ( k2_lattices(sK9,X0,sK2(sK9,X0)) != X0
% 7.75/1.51      | k2_lattices(sK9,sK2(sK9,X0),X0) != X0
% 7.75/1.51      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | v13_lattices(sK9) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14929,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X0))) != k15_lattice3(sK9,X0)
% 7.75/1.51      | m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | v13_lattices(sK9) = iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_14802,c_3068]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14951,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK2(sK9,k15_lattice3(sK9,k1_xboole_0))) != k15_lattice3(sK9,k1_xboole_0)
% 7.75/1.51      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | v13_lattices(sK9) = iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_14929]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3225,plain,
% 7.75/1.51      ( ~ r3_lattices(sK9,k15_lattice3(sK9,X0),X1)
% 7.75/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
% 7.75/1.51      | k2_lattices(sK9,k15_lattice3(sK9,X0),X1) = k15_lattice3(sK9,X0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1165]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3905,plain,
% 7.75/1.51      ( ~ r3_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X1)))
% 7.75/1.51      | ~ m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
% 7.75/1.51      | ~ m1_subset_1(sK2(sK9,k15_lattice3(sK9,X1)),u1_struct_0(sK9))
% 7.75/1.51      | k2_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X1))) = k15_lattice3(sK9,X0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_3225]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3911,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X1))) = k15_lattice3(sK9,X0)
% 7.75/1.51      | r3_lattices(sK9,k15_lattice3(sK9,X0),sK2(sK9,k15_lattice3(sK9,X1))) != iProver_top
% 7.75/1.51      | m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(sK2(sK9,k15_lattice3(sK9,X1)),u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_3905]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3913,plain,
% 7.75/1.51      ( k2_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK2(sK9,k15_lattice3(sK9,k1_xboole_0))) = k15_lattice3(sK9,k1_xboole_0)
% 7.75/1.51      | r3_lattices(sK9,k15_lattice3(sK9,k1_xboole_0),sK2(sK9,k15_lattice3(sK9,k1_xboole_0))) != iProver_top
% 7.75/1.51      | m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_3911]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3156,plain,
% 7.75/1.51      ( ~ m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9))
% 7.75/1.51      | m1_subset_1(sK2(sK9,k15_lattice3(sK9,X0)),u1_struct_0(sK9))
% 7.75/1.51      | v13_lattices(sK9) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1438]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3157,plain,
% 7.75/1.51      ( m1_subset_1(k15_lattice3(sK9,X0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(sK2(sK9,k15_lattice3(sK9,X0)),u1_struct_0(sK9)) = iProver_top
% 7.75/1.51      | v13_lattices(sK9) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_3156]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3159,plain,
% 7.75/1.51      ( m1_subset_1(k15_lattice3(sK9,k1_xboole_0),u1_struct_0(sK9)) != iProver_top
% 7.75/1.51      | m1_subset_1(sK2(sK9,k15_lattice3(sK9,k1_xboole_0)),u1_struct_0(sK9)) = iProver_top
% 7.75/1.51      | v13_lattices(sK9) = iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_3157]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(contradiction,plain,
% 7.75/1.51      ( $false ),
% 7.75/1.51      inference(minisat,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_15634,c_14954,c_14951,c_12033,c_3913,c_3159,c_1210,
% 7.75/1.51                 c_47]) ).
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.51  
% 7.75/1.51  ------                               Statistics
% 7.75/1.51  
% 7.75/1.51  ------ General
% 7.75/1.51  
% 7.75/1.51  abstr_ref_over_cycles:                  0
% 7.75/1.51  abstr_ref_under_cycles:                 0
% 7.75/1.51  gc_basic_clause_elim:                   0
% 7.75/1.51  forced_gc_time:                         0
% 7.75/1.51  parsing_time:                           0.011
% 7.75/1.51  unif_index_cands_time:                  0.
% 7.75/1.51  unif_index_add_time:                    0.
% 7.75/1.51  orderings_time:                         0.
% 7.75/1.51  out_proof_time:                         0.031
% 7.75/1.51  total_time:                             0.61
% 7.75/1.51  num_of_symbols:                         64
% 7.75/1.51  num_of_terms:                           19391
% 7.75/1.51  
% 7.75/1.51  ------ Preprocessing
% 7.75/1.51  
% 7.75/1.51  num_of_splits:                          0
% 7.75/1.51  num_of_split_atoms:                     0
% 7.75/1.51  num_of_reused_defs:                     0
% 7.75/1.51  num_eq_ax_congr_red:                    55
% 7.75/1.51  num_of_sem_filtered_clauses:            1
% 7.75/1.51  num_of_subtypes:                        0
% 7.75/1.51  monotx_restored_types:                  0
% 7.75/1.51  sat_num_of_epr_types:                   0
% 7.75/1.51  sat_num_of_non_cyclic_types:            0
% 7.75/1.51  sat_guarded_non_collapsed_types:        0
% 7.75/1.51  num_pure_diseq_elim:                    0
% 7.75/1.51  simp_replaced_by:                       0
% 7.75/1.51  res_preprocessed:                       185
% 7.75/1.51  prep_upred:                             0
% 7.75/1.51  prep_unflattend:                        42
% 7.75/1.51  smt_new_axioms:                         0
% 7.75/1.51  pred_elim_cands:                        4
% 7.75/1.51  pred_elim:                              10
% 7.75/1.51  pred_elim_cl:                           14
% 7.75/1.51  pred_elim_cycles:                       14
% 7.75/1.51  merged_defs:                            0
% 7.75/1.51  merged_defs_ncl:                        0
% 7.75/1.51  bin_hyper_res:                          0
% 7.75/1.51  prep_cycles:                            4
% 7.75/1.51  pred_elim_time:                         0.024
% 7.75/1.51  splitting_time:                         0.
% 7.75/1.51  sem_filter_time:                        0.
% 7.75/1.51  monotx_time:                            0.
% 7.75/1.51  subtype_inf_time:                       0.
% 7.75/1.51  
% 7.75/1.51  ------ Problem properties
% 7.75/1.51  
% 7.75/1.51  clauses:                                32
% 7.75/1.51  conjectures:                            1
% 7.75/1.51  epr:                                    0
% 7.75/1.51  horn:                                   26
% 7.75/1.51  ground:                                 3
% 7.75/1.51  unary:                                  5
% 7.75/1.51  binary:                                 13
% 7.75/1.51  lits:                                   82
% 7.75/1.51  lits_eq:                                24
% 7.75/1.51  fd_pure:                                0
% 7.75/1.51  fd_pseudo:                              0
% 7.75/1.51  fd_cond:                                5
% 7.75/1.51  fd_pseudo_cond:                         0
% 7.75/1.51  ac_symbols:                             0
% 7.75/1.51  
% 7.75/1.51  ------ Propositional Solver
% 7.75/1.51  
% 7.75/1.51  prop_solver_calls:                      29
% 7.75/1.51  prop_fast_solver_calls:                 2411
% 7.75/1.51  smt_solver_calls:                       0
% 7.75/1.51  smt_fast_solver_calls:                  0
% 7.75/1.51  prop_num_of_clauses:                    7443
% 7.75/1.51  prop_preprocess_simplified:             13124
% 7.75/1.51  prop_fo_subsumed:                       145
% 7.75/1.51  prop_solver_time:                       0.
% 7.75/1.51  smt_solver_time:                        0.
% 7.75/1.51  smt_fast_solver_time:                   0.
% 7.75/1.51  prop_fast_solver_time:                  0.
% 7.75/1.51  prop_unsat_core_time:                   0.
% 7.75/1.51  
% 7.75/1.51  ------ QBF
% 7.75/1.51  
% 7.75/1.51  qbf_q_res:                              0
% 7.75/1.51  qbf_num_tautologies:                    0
% 7.75/1.51  qbf_prep_cycles:                        0
% 7.75/1.51  
% 7.75/1.51  ------ BMC1
% 7.75/1.51  
% 7.75/1.51  bmc1_current_bound:                     -1
% 7.75/1.51  bmc1_last_solved_bound:                 -1
% 7.75/1.51  bmc1_unsat_core_size:                   -1
% 7.75/1.51  bmc1_unsat_core_parents_size:           -1
% 7.75/1.51  bmc1_merge_next_fun:                    0
% 7.75/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.75/1.51  
% 7.75/1.51  ------ Instantiation
% 7.75/1.51  
% 7.75/1.51  inst_num_of_clauses:                    1770
% 7.75/1.51  inst_num_in_passive:                    21
% 7.75/1.51  inst_num_in_active:                     927
% 7.75/1.51  inst_num_in_unprocessed:                823
% 7.75/1.51  inst_num_of_loops:                      1280
% 7.75/1.51  inst_num_of_learning_restarts:          0
% 7.75/1.51  inst_num_moves_active_passive:          349
% 7.75/1.51  inst_lit_activity:                      0
% 7.75/1.51  inst_lit_activity_moves:                0
% 7.75/1.51  inst_num_tautologies:                   0
% 7.75/1.51  inst_num_prop_implied:                  0
% 7.75/1.51  inst_num_existing_simplified:           0
% 7.75/1.51  inst_num_eq_res_simplified:             0
% 7.75/1.51  inst_num_child_elim:                    0
% 7.75/1.51  inst_num_of_dismatching_blockings:      1093
% 7.75/1.51  inst_num_of_non_proper_insts:           2178
% 7.75/1.51  inst_num_of_duplicates:                 0
% 7.75/1.51  inst_inst_num_from_inst_to_res:         0
% 7.75/1.51  inst_dismatching_checking_time:         0.
% 7.75/1.51  
% 7.75/1.51  ------ Resolution
% 7.75/1.51  
% 7.75/1.51  res_num_of_clauses:                     0
% 7.75/1.51  res_num_in_passive:                     0
% 7.75/1.51  res_num_in_active:                      0
% 7.75/1.51  res_num_of_loops:                       189
% 7.75/1.51  res_forward_subset_subsumed:            129
% 7.75/1.51  res_backward_subset_subsumed:           2
% 7.75/1.51  res_forward_subsumed:                   0
% 7.75/1.51  res_backward_subsumed:                  0
% 7.75/1.51  res_forward_subsumption_resolution:     1
% 7.75/1.51  res_backward_subsumption_resolution:    0
% 7.75/1.51  res_clause_to_clause_subsumption:       3582
% 7.75/1.51  res_orphan_elimination:                 0
% 7.75/1.51  res_tautology_del:                      228
% 7.75/1.51  res_num_eq_res_simplified:              0
% 7.75/1.51  res_num_sel_changes:                    0
% 7.75/1.51  res_moves_from_active_to_pass:          0
% 7.75/1.51  
% 7.75/1.51  ------ Superposition
% 7.75/1.51  
% 7.75/1.51  sup_time_total:                         0.
% 7.75/1.51  sup_time_generating:                    0.
% 7.75/1.51  sup_time_sim_full:                      0.
% 7.75/1.51  sup_time_sim_immed:                     0.
% 7.75/1.51  
% 7.75/1.51  sup_num_of_clauses:                     885
% 7.75/1.51  sup_num_in_active:                      161
% 7.75/1.51  sup_num_in_passive:                     724
% 7.75/1.51  sup_num_of_loops:                       254
% 7.75/1.51  sup_fw_superposition:                   985
% 7.75/1.51  sup_bw_superposition:                   330
% 7.75/1.51  sup_immediate_simplified:               252
% 7.75/1.51  sup_given_eliminated:                   1
% 7.75/1.51  comparisons_done:                       0
% 7.75/1.51  comparisons_avoided:                    146
% 7.75/1.51  
% 7.75/1.51  ------ Simplifications
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  sim_fw_subset_subsumed:                 68
% 7.75/1.51  sim_bw_subset_subsumed:                 5
% 7.75/1.51  sim_fw_subsumed:                        80
% 7.75/1.51  sim_bw_subsumed:                        96
% 7.75/1.51  sim_fw_subsumption_res:                 0
% 7.75/1.51  sim_bw_subsumption_res:                 0
% 7.75/1.51  sim_tautology_del:                      12
% 7.75/1.51  sim_eq_tautology_del:                   41
% 7.75/1.51  sim_eq_res_simp:                        0
% 7.75/1.51  sim_fw_demodulated:                     57
% 7.75/1.51  sim_bw_demodulated:                     4
% 7.75/1.51  sim_light_normalised:                   124
% 7.75/1.51  sim_joinable_taut:                      0
% 7.75/1.51  sim_joinable_simp:                      0
% 7.75/1.51  sim_ac_normalised:                      0
% 7.75/1.51  sim_smt_subsumption:                    0
% 7.75/1.51  
%------------------------------------------------------------------------------
