%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1205+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:09 EST 2020

% Result     : Theorem 1.20s
% Output     : CNFRefutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 336 expanded)
%              Number of clauses        :   57 (  86 expanded)
%              Number of leaves         :   14 (  86 expanded)
%              Depth                    :   17
%              Number of atoms          :  454 (1650 expanded)
%              Number of equality atoms :  114 ( 307 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k3_lattices(X0,k5_lattices(X0),sK4) != sK4
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_lattices(X0,k5_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k3_lattices(sK3,k5_lattices(sK3),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v13_lattices(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k3_lattices(sK3,k5_lattices(sK3),sK4) != sK4
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v13_lattices(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f36,f35])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK2(X0)),sK2(X0)) != sK2(X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK1(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK1(X0),sK2(X0)),sK2(X0)) != sK2(X0)
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).

fof(f45,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
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

fof(f9,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f40,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f55,plain,(
    v13_lattices(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    k3_lattices(sK3,k5_lattices(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_406,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_407,plain,
    ( m1_subset_1(k5_lattices(sK3),u1_struct_0(sK3))
    | ~ l1_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_17,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_30,plain,
    ( l1_lattices(sK3)
    | ~ l3_lattices(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_36,plain,
    ( m1_subset_1(k5_lattices(sK3),u1_struct_0(sK3))
    | ~ l1_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_409,plain,
    ( m1_subset_1(k5_lattices(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_20,c_17,c_30,c_36])).

cnf(c_479,plain,
    ( m1_subset_1(k5_lattices(sK3),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_649,plain,
    ( m1_subset_1(k5_lattices(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_486,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_642,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_284,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v8_lattices(sK3)
    | k1_lattices(sK3,k2_lattices(sK3,X1,X0),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_19,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v8_lattices(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_67,plain,
    ( ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3)
    | v8_lattices(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k1_lattices(sK3,k2_lattices(sK3,X1,X0),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_284,c_20,c_19,c_17,c_67])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK3))
    | k1_lattices(sK3,k2_lattices(sK3,X1_47,X0_47),X0_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_288])).

cnf(c_644,plain,
    ( k1_lattices(sK3,k2_lattices(sK3,X0_47,X1_47),X1_47) = X1_47
    | m1_subset_1(X0_47,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_854,plain,
    ( k1_lattices(sK3,k2_lattices(sK3,X0_47,sK4),sK4) = sK4
    | m1_subset_1(X0_47,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_642,c_644])).

cnf(c_920,plain,
    ( k1_lattices(sK3,k2_lattices(sK3,k5_lattices(sK3),sK4),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_649,c_854])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( v13_lattices(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k5_lattices(sK3),u1_struct_0(sK3))
    | ~ l1_lattices(sK3)
    | v2_struct_0(sK3)
    | k2_lattices(sK3,k5_lattices(sK3),X0) = k5_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k2_lattices(sK3,k5_lattices(sK3),X0) = k5_lattices(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_20,c_17,c_30,c_36])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK3))
    | k2_lattices(sK3,k5_lattices(sK3),X0_47) = k5_lattices(sK3) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_645,plain,
    ( k2_lattices(sK3,k5_lattices(sK3),X0_47) = k5_lattices(sK3)
    | m1_subset_1(X0_47,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_737,plain,
    ( k2_lattices(sK3,k5_lattices(sK3),sK4) = k5_lattices(sK3) ),
    inference(superposition,[status(thm)],[c_642,c_645])).

cnf(c_922,plain,
    ( k1_lattices(sK3,k5_lattices(sK3),sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_920,c_737])).

cnf(c_490,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_743,plain,
    ( k1_lattices(sK3,k5_lattices(sK3),sK4) != X0_47
    | sK4 != X0_47
    | sK4 = k1_lattices(sK3,k5_lattices(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_744,plain,
    ( k1_lattices(sK3,k5_lattices(sK3),sK4) != sK4
    | sK4 = k1_lattices(sK3,k5_lattices(sK3),sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_219,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_220,plain,
    ( v4_lattices(sK3)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_64,plain,
    ( v4_lattices(sK3)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_222,plain,
    ( v4_lattices(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_220,c_20,c_19,c_17,c_64])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_222])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l2_lattices(sK3)
    | v2_struct_0(sK3)
    | k3_lattices(sK3,X1,X0) = k1_lattices(sK3,X1,X0) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_12,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_33,plain,
    ( l2_lattices(sK3)
    | ~ l3_lattices(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k3_lattices(sK3,X1,X0) = k1_lattices(sK3,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_246,c_20,c_17,c_33])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK3))
    | k3_lattices(sK3,X1_47,X0_47) = k1_lattices(sK3,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_250])).

cnf(c_718,plain,
    ( ~ m1_subset_1(k5_lattices(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k3_lattices(sK3,k5_lattices(sK3),sK4) = k1_lattices(sK3,k5_lattices(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_710,plain,
    ( k3_lattices(sK3,k5_lattices(sK3),sK4) != X0_47
    | k3_lattices(sK3,k5_lattices(sK3),sK4) = sK4
    | sK4 != X0_47 ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_717,plain,
    ( k3_lattices(sK3,k5_lattices(sK3),sK4) != k1_lattices(sK3,k5_lattices(sK3),sK4)
    | k3_lattices(sK3,k5_lattices(sK3),sK4) = sK4
    | sK4 != k1_lattices(sK3,k5_lattices(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_15,negated_conjecture,
    ( k3_lattices(sK3,k5_lattices(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_487,negated_conjecture,
    ( k3_lattices(sK3,k5_lattices(sK3),sK4) != sK4 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_489,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_500,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_922,c_744,c_718,c_717,c_487,c_500,c_36,c_30,c_16,c_17,c_20])).


%------------------------------------------------------------------------------
