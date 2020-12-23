%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:17 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 358 expanded)
%              Number of clauses        :   77 ( 105 expanded)
%              Number of leaves         :   15 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          :  519 (1740 expanded)
%              Number of equality atoms :  129 ( 334 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),sK3)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),X1)
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l3_lattices(sK2)
      & v13_lattices(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v13_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f34,f33])).

fof(f54,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    v13_lattices(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f38,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
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

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK1(X0))) != X1
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK0(X0),k1_lattices(X0,sK0(X0),X2)) != sK0(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK0(X0),k1_lattices(X0,sK0(X0),sK1(X0))) != sK0(X0)
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f40,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_505,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_627,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_10,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_297,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_8])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_409,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_19])).

cnf(c_410,plain,
    ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
    | ~ l3_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_16,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_35,plain,
    ( l1_lattices(sK2)
    | ~ l3_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_41,plain,
    ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
    | ~ l1_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_412,plain,
    ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_19,c_16,c_35,c_41])).

cnf(c_501,plain,
    ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_412])).

cnf(c_631,plain,
    ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_2,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_231,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_231])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_18,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_316,c_18])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k3_lattices(sK2,X1,X0) = k1_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k3_lattices(sK2,X1,X0) = k1_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_19,c_16])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | k3_lattices(sK2,X1_48,X0_48) = k1_lattices(sK2,X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_629,plain,
    ( k3_lattices(sK2,X0_48,X1_48) = k1_lattices(sK2,X0_48,X1_48)
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_748,plain,
    ( k3_lattices(sK2,k5_lattices(sK2),X0_48) = k1_lattices(sK2,k5_lattices(sK2),X0_48)
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_631,c_629])).

cnf(c_1228,plain,
    ( k3_lattices(sK2,k5_lattices(sK2),sK3) = k1_lattices(sK2,k5_lattices(sK2),sK3) ),
    inference(superposition,[status(thm)],[c_627,c_748])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,negated_conjecture,
    ( v13_lattices(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | k3_lattices(sK2,k5_lattices(sK2),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k3_lattices(sK2,k5_lattices(sK2),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_210,c_19,c_18,c_16])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | k3_lattices(sK2,k5_lattices(sK2),X0_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_214])).

cnf(c_628,plain,
    ( k3_lattices(sK2,k5_lattices(sK2),X0_48) = X0_48
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_700,plain,
    ( k3_lattices(sK2,k5_lattices(sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_627,c_628])).

cnf(c_1234,plain,
    ( k1_lattices(sK2,k5_lattices(sK2),sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_1228,c_700])).

cnf(c_510,plain,
    ( X0_48 != X1_48
    | k2_lattices(X0_50,X2_48,X0_48) = k2_lattices(X0_50,X2_48,X1_48) ),
    theory(equality)).

cnf(c_1139,plain,
    ( k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) = k2_lattices(sK2,k5_lattices(sK2),X1_48)
    | k1_lattices(sK2,k5_lattices(sK2),X0_48) != X1_48 ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_1141,plain,
    ( k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) = k2_lattices(sK2,k5_lattices(sK2),sK3)
    | k1_lattices(sK2,k5_lattices(sK2),sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_509,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_797,plain,
    ( k4_lattices(sK2,k5_lattices(sK2),sK3) != X0_48
    | k4_lattices(sK2,k5_lattices(sK2),sK3) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X1_48))
    | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X1_48)) != X0_48 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_1018,plain,
    ( k4_lattices(sK2,k5_lattices(sK2),sK3) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48))
    | k4_lattices(sK2,k5_lattices(sK2),sK3) != k2_lattices(sK2,k5_lattices(sK2),sK3)
    | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) != k2_lattices(sK2,k5_lattices(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_1019,plain,
    ( k4_lattices(sK2,k5_lattices(sK2),sK3) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3))
    | k4_lattices(sK2,k5_lattices(sK2),sK3) != k2_lattices(sK2,k5_lattices(sK2),sK3)
    | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) != k2_lattices(sK2,k5_lattices(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_1,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_262,c_10])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_280,c_18])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k4_lattices(sK2,X1,X0) = k2_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k4_lattices(sK2,X1,X0) = k2_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_19,c_16])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | k4_lattices(sK2,X1_48,X0_48) = k2_lattices(sK2,X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_383])).

cnf(c_821,plain,
    ( ~ m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k4_lattices(sK2,k5_lattices(sK2),sK3) = k2_lattices(sK2,k5_lattices(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_674,plain,
    ( k4_lattices(sK2,k5_lattices(sK2),sK3) != X0_48
    | k5_lattices(sK2) != X0_48
    | k5_lattices(sK2) = k4_lattices(sK2,k5_lattices(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_763,plain,
    ( k4_lattices(sK2,k5_lattices(sK2),sK3) != k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48))
    | k5_lattices(sK2) = k4_lattices(sK2,k5_lattices(sK2),sK3)
    | k5_lattices(sK2) != k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_764,plain,
    ( k4_lattices(sK2,k5_lattices(sK2),sK3) != k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3))
    | k5_lattices(sK2) = k4_lattices(sK2,k5_lattices(sK2),sK3)
    | k5_lattices(sK2) != k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | ~ v9_lattices(sK2)
    | k2_lattices(sK2,X1,k1_lattices(sK2,X1,X0)) = X1 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_63,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | v9_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X1,k1_lattices(sK2,X1,X0)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_19,c_18,c_16,c_63])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | k2_lattices(sK2,X1_48,k1_lattices(sK2,X1_48,X0_48)) = X1_48 ),
    inference(subtyping,[status(esa)],[c_431])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
    | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) = k5_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_719,plain,
    ( ~ m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) = k5_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_687,plain,
    ( X0_48 != X1_48
    | k5_lattices(sK2) != X1_48
    | k5_lattices(sK2) = X0_48 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_709,plain,
    ( X0_48 != k5_lattices(sK2)
    | k5_lattices(sK2) = X0_48
    | k5_lattices(sK2) != k5_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_715,plain,
    ( k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) != k5_lattices(sK2)
    | k5_lattices(sK2) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48))
    | k5_lattices(sK2) != k5_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_717,plain,
    ( k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) != k5_lattices(sK2)
    | k5_lattices(sK2) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3))
    | k5_lattices(sK2) != k5_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_508,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_686,plain,
    ( k5_lattices(sK2) = k5_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_14,negated_conjecture,
    ( k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_506,negated_conjecture,
    ( k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),sK3) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1234,c_1141,c_1019,c_821,c_764,c_719,c_717,c_686,c_506,c_41,c_35,c_15,c_16,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:20:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.55/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.02  
% 1.55/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.55/1.02  
% 1.55/1.02  ------  iProver source info
% 1.55/1.02  
% 1.55/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.55/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.55/1.02  git: non_committed_changes: false
% 1.55/1.02  git: last_make_outside_of_git: false
% 1.55/1.02  
% 1.55/1.02  ------ 
% 1.55/1.02  
% 1.55/1.02  ------ Input Options
% 1.55/1.02  
% 1.55/1.02  --out_options                           all
% 1.55/1.02  --tptp_safe_out                         true
% 1.55/1.02  --problem_path                          ""
% 1.55/1.02  --include_path                          ""
% 1.55/1.02  --clausifier                            res/vclausify_rel
% 1.55/1.02  --clausifier_options                    --mode clausify
% 1.55/1.02  --stdin                                 false
% 1.55/1.02  --stats_out                             all
% 1.55/1.02  
% 1.55/1.02  ------ General Options
% 1.55/1.02  
% 1.55/1.02  --fof                                   false
% 1.55/1.02  --time_out_real                         305.
% 1.55/1.02  --time_out_virtual                      -1.
% 1.55/1.02  --symbol_type_check                     false
% 1.55/1.02  --clausify_out                          false
% 1.55/1.02  --sig_cnt_out                           false
% 1.55/1.02  --trig_cnt_out                          false
% 1.55/1.02  --trig_cnt_out_tolerance                1.
% 1.55/1.02  --trig_cnt_out_sk_spl                   false
% 1.55/1.02  --abstr_cl_out                          false
% 1.55/1.02  
% 1.55/1.02  ------ Global Options
% 1.55/1.02  
% 1.55/1.02  --schedule                              default
% 1.55/1.02  --add_important_lit                     false
% 1.55/1.02  --prop_solver_per_cl                    1000
% 1.55/1.02  --min_unsat_core                        false
% 1.55/1.02  --soft_assumptions                      false
% 1.55/1.02  --soft_lemma_size                       3
% 1.55/1.02  --prop_impl_unit_size                   0
% 1.55/1.02  --prop_impl_unit                        []
% 1.55/1.02  --share_sel_clauses                     true
% 1.55/1.02  --reset_solvers                         false
% 1.55/1.02  --bc_imp_inh                            [conj_cone]
% 1.55/1.02  --conj_cone_tolerance                   3.
% 1.55/1.02  --extra_neg_conj                        none
% 1.55/1.02  --large_theory_mode                     true
% 1.55/1.02  --prolific_symb_bound                   200
% 1.55/1.02  --lt_threshold                          2000
% 1.55/1.02  --clause_weak_htbl                      true
% 1.55/1.02  --gc_record_bc_elim                     false
% 1.55/1.02  
% 1.55/1.02  ------ Preprocessing Options
% 1.55/1.02  
% 1.55/1.02  --preprocessing_flag                    true
% 1.55/1.02  --time_out_prep_mult                    0.1
% 1.55/1.02  --splitting_mode                        input
% 1.55/1.02  --splitting_grd                         true
% 1.55/1.02  --splitting_cvd                         false
% 1.55/1.02  --splitting_cvd_svl                     false
% 1.55/1.02  --splitting_nvd                         32
% 1.55/1.02  --sub_typing                            true
% 1.55/1.02  --prep_gs_sim                           true
% 1.55/1.02  --prep_unflatten                        true
% 1.55/1.02  --prep_res_sim                          true
% 1.55/1.02  --prep_upred                            true
% 1.55/1.02  --prep_sem_filter                       exhaustive
% 1.55/1.02  --prep_sem_filter_out                   false
% 1.55/1.02  --pred_elim                             true
% 1.55/1.02  --res_sim_input                         true
% 1.55/1.02  --eq_ax_congr_red                       true
% 1.55/1.02  --pure_diseq_elim                       true
% 1.55/1.02  --brand_transform                       false
% 1.55/1.02  --non_eq_to_eq                          false
% 1.55/1.02  --prep_def_merge                        true
% 1.55/1.02  --prep_def_merge_prop_impl              false
% 1.55/1.02  --prep_def_merge_mbd                    true
% 1.55/1.02  --prep_def_merge_tr_red                 false
% 1.55/1.02  --prep_def_merge_tr_cl                  false
% 1.55/1.02  --smt_preprocessing                     true
% 1.55/1.02  --smt_ac_axioms                         fast
% 1.55/1.02  --preprocessed_out                      false
% 1.55/1.02  --preprocessed_stats                    false
% 1.55/1.02  
% 1.55/1.02  ------ Abstraction refinement Options
% 1.55/1.02  
% 1.55/1.02  --abstr_ref                             []
% 1.55/1.02  --abstr_ref_prep                        false
% 1.55/1.02  --abstr_ref_until_sat                   false
% 1.55/1.02  --abstr_ref_sig_restrict                funpre
% 1.55/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/1.02  --abstr_ref_under                       []
% 1.55/1.02  
% 1.55/1.02  ------ SAT Options
% 1.55/1.02  
% 1.55/1.02  --sat_mode                              false
% 1.55/1.02  --sat_fm_restart_options                ""
% 1.55/1.02  --sat_gr_def                            false
% 1.55/1.02  --sat_epr_types                         true
% 1.55/1.02  --sat_non_cyclic_types                  false
% 1.55/1.02  --sat_finite_models                     false
% 1.55/1.02  --sat_fm_lemmas                         false
% 1.55/1.02  --sat_fm_prep                           false
% 1.55/1.02  --sat_fm_uc_incr                        true
% 1.55/1.02  --sat_out_model                         small
% 1.55/1.02  --sat_out_clauses                       false
% 1.55/1.02  
% 1.55/1.02  ------ QBF Options
% 1.55/1.02  
% 1.55/1.02  --qbf_mode                              false
% 1.55/1.02  --qbf_elim_univ                         false
% 1.55/1.02  --qbf_dom_inst                          none
% 1.55/1.02  --qbf_dom_pre_inst                      false
% 1.55/1.02  --qbf_sk_in                             false
% 1.55/1.02  --qbf_pred_elim                         true
% 1.55/1.02  --qbf_split                             512
% 1.55/1.02  
% 1.55/1.02  ------ BMC1 Options
% 1.55/1.02  
% 1.55/1.02  --bmc1_incremental                      false
% 1.55/1.02  --bmc1_axioms                           reachable_all
% 1.55/1.02  --bmc1_min_bound                        0
% 1.55/1.02  --bmc1_max_bound                        -1
% 1.55/1.02  --bmc1_max_bound_default                -1
% 1.55/1.02  --bmc1_symbol_reachability              true
% 1.55/1.02  --bmc1_property_lemmas                  false
% 1.55/1.02  --bmc1_k_induction                      false
% 1.55/1.02  --bmc1_non_equiv_states                 false
% 1.55/1.02  --bmc1_deadlock                         false
% 1.55/1.02  --bmc1_ucm                              false
% 1.55/1.02  --bmc1_add_unsat_core                   none
% 1.55/1.02  --bmc1_unsat_core_children              false
% 1.55/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/1.02  --bmc1_out_stat                         full
% 1.55/1.02  --bmc1_ground_init                      false
% 1.55/1.02  --bmc1_pre_inst_next_state              false
% 1.55/1.02  --bmc1_pre_inst_state                   false
% 1.55/1.02  --bmc1_pre_inst_reach_state             false
% 1.55/1.02  --bmc1_out_unsat_core                   false
% 1.55/1.02  --bmc1_aig_witness_out                  false
% 1.55/1.02  --bmc1_verbose                          false
% 1.55/1.02  --bmc1_dump_clauses_tptp                false
% 1.55/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.55/1.02  --bmc1_dump_file                        -
% 1.55/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.55/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.55/1.02  --bmc1_ucm_extend_mode                  1
% 1.55/1.02  --bmc1_ucm_init_mode                    2
% 1.55/1.02  --bmc1_ucm_cone_mode                    none
% 1.55/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.55/1.02  --bmc1_ucm_relax_model                  4
% 1.55/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.55/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/1.02  --bmc1_ucm_layered_model                none
% 1.55/1.02  --bmc1_ucm_max_lemma_size               10
% 1.55/1.02  
% 1.55/1.02  ------ AIG Options
% 1.55/1.02  
% 1.55/1.02  --aig_mode                              false
% 1.55/1.02  
% 1.55/1.02  ------ Instantiation Options
% 1.55/1.02  
% 1.55/1.02  --instantiation_flag                    true
% 1.55/1.02  --inst_sos_flag                         false
% 1.55/1.02  --inst_sos_phase                        true
% 1.55/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/1.02  --inst_lit_sel_side                     num_symb
% 1.55/1.02  --inst_solver_per_active                1400
% 1.55/1.02  --inst_solver_calls_frac                1.
% 1.55/1.02  --inst_passive_queue_type               priority_queues
% 1.55/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/1.02  --inst_passive_queues_freq              [25;2]
% 1.55/1.02  --inst_dismatching                      true
% 1.55/1.02  --inst_eager_unprocessed_to_passive     true
% 1.55/1.02  --inst_prop_sim_given                   true
% 1.55/1.02  --inst_prop_sim_new                     false
% 1.55/1.02  --inst_subs_new                         false
% 1.55/1.02  --inst_eq_res_simp                      false
% 1.55/1.02  --inst_subs_given                       false
% 1.55/1.02  --inst_orphan_elimination               true
% 1.55/1.02  --inst_learning_loop_flag               true
% 1.55/1.02  --inst_learning_start                   3000
% 1.55/1.02  --inst_learning_factor                  2
% 1.55/1.02  --inst_start_prop_sim_after_learn       3
% 1.55/1.02  --inst_sel_renew                        solver
% 1.55/1.02  --inst_lit_activity_flag                true
% 1.55/1.02  --inst_restr_to_given                   false
% 1.55/1.02  --inst_activity_threshold               500
% 1.55/1.02  --inst_out_proof                        true
% 1.55/1.02  
% 1.55/1.02  ------ Resolution Options
% 1.55/1.02  
% 1.55/1.02  --resolution_flag                       true
% 1.55/1.02  --res_lit_sel                           adaptive
% 1.55/1.02  --res_lit_sel_side                      none
% 1.55/1.02  --res_ordering                          kbo
% 1.55/1.02  --res_to_prop_solver                    active
% 1.55/1.02  --res_prop_simpl_new                    false
% 1.55/1.02  --res_prop_simpl_given                  true
% 1.55/1.02  --res_passive_queue_type                priority_queues
% 1.55/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/1.02  --res_passive_queues_freq               [15;5]
% 1.55/1.02  --res_forward_subs                      full
% 1.55/1.02  --res_backward_subs                     full
% 1.55/1.02  --res_forward_subs_resolution           true
% 1.55/1.02  --res_backward_subs_resolution          true
% 1.55/1.02  --res_orphan_elimination                true
% 1.55/1.02  --res_time_limit                        2.
% 1.55/1.02  --res_out_proof                         true
% 1.55/1.02  
% 1.55/1.02  ------ Superposition Options
% 1.55/1.02  
% 1.55/1.02  --superposition_flag                    true
% 1.55/1.02  --sup_passive_queue_type                priority_queues
% 1.55/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.55/1.02  --demod_completeness_check              fast
% 1.55/1.02  --demod_use_ground                      true
% 1.55/1.02  --sup_to_prop_solver                    passive
% 1.55/1.02  --sup_prop_simpl_new                    true
% 1.55/1.02  --sup_prop_simpl_given                  true
% 1.55/1.02  --sup_fun_splitting                     false
% 1.55/1.02  --sup_smt_interval                      50000
% 1.55/1.02  
% 1.55/1.02  ------ Superposition Simplification Setup
% 1.55/1.02  
% 1.55/1.02  --sup_indices_passive                   []
% 1.55/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.02  --sup_full_bw                           [BwDemod]
% 1.55/1.02  --sup_immed_triv                        [TrivRules]
% 1.55/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.02  --sup_immed_bw_main                     []
% 1.55/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.02  
% 1.55/1.02  ------ Combination Options
% 1.55/1.02  
% 1.55/1.02  --comb_res_mult                         3
% 1.55/1.02  --comb_sup_mult                         2
% 1.55/1.02  --comb_inst_mult                        10
% 1.55/1.02  
% 1.55/1.02  ------ Debug Options
% 1.55/1.02  
% 1.55/1.02  --dbg_backtrace                         false
% 1.55/1.02  --dbg_dump_prop_clauses                 false
% 1.55/1.02  --dbg_dump_prop_clauses_file            -
% 1.55/1.02  --dbg_out_stat                          false
% 1.55/1.02  ------ Parsing...
% 1.55/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.55/1.02  
% 1.55/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.55/1.02  
% 1.55/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.55/1.02  
% 1.55/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.55/1.02  ------ Proving...
% 1.55/1.02  ------ Problem Properties 
% 1.55/1.02  
% 1.55/1.02  
% 1.55/1.02  clauses                                 7
% 1.55/1.02  conjectures                             2
% 1.55/1.02  EPR                                     0
% 1.55/1.02  Horn                                    7
% 1.55/1.02  unary                                   3
% 1.55/1.02  binary                                  1
% 1.55/1.02  lits                                    14
% 1.55/1.02  lits eq                                 5
% 1.55/1.02  fd_pure                                 0
% 1.55/1.02  fd_pseudo                               0
% 1.55/1.02  fd_cond                                 0
% 1.55/1.02  fd_pseudo_cond                          0
% 1.55/1.02  AC symbols                              0
% 1.55/1.02  
% 1.55/1.02  ------ Schedule dynamic 5 is on 
% 1.55/1.02  
% 1.55/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.55/1.02  
% 1.55/1.02  
% 1.55/1.02  ------ 
% 1.55/1.02  Current options:
% 1.55/1.02  ------ 
% 1.55/1.02  
% 1.55/1.02  ------ Input Options
% 1.55/1.02  
% 1.55/1.02  --out_options                           all
% 1.55/1.02  --tptp_safe_out                         true
% 1.55/1.02  --problem_path                          ""
% 1.55/1.02  --include_path                          ""
% 1.55/1.02  --clausifier                            res/vclausify_rel
% 1.55/1.02  --clausifier_options                    --mode clausify
% 1.55/1.02  --stdin                                 false
% 1.55/1.02  --stats_out                             all
% 1.55/1.02  
% 1.55/1.02  ------ General Options
% 1.55/1.02  
% 1.55/1.02  --fof                                   false
% 1.55/1.02  --time_out_real                         305.
% 1.55/1.02  --time_out_virtual                      -1.
% 1.55/1.02  --symbol_type_check                     false
% 1.55/1.02  --clausify_out                          false
% 1.55/1.02  --sig_cnt_out                           false
% 1.55/1.02  --trig_cnt_out                          false
% 1.55/1.02  --trig_cnt_out_tolerance                1.
% 1.55/1.02  --trig_cnt_out_sk_spl                   false
% 1.55/1.02  --abstr_cl_out                          false
% 1.55/1.02  
% 1.55/1.02  ------ Global Options
% 1.55/1.02  
% 1.55/1.02  --schedule                              default
% 1.55/1.02  --add_important_lit                     false
% 1.55/1.02  --prop_solver_per_cl                    1000
% 1.55/1.02  --min_unsat_core                        false
% 1.55/1.02  --soft_assumptions                      false
% 1.55/1.02  --soft_lemma_size                       3
% 1.55/1.02  --prop_impl_unit_size                   0
% 1.55/1.02  --prop_impl_unit                        []
% 1.55/1.02  --share_sel_clauses                     true
% 1.55/1.02  --reset_solvers                         false
% 1.55/1.02  --bc_imp_inh                            [conj_cone]
% 1.55/1.02  --conj_cone_tolerance                   3.
% 1.55/1.02  --extra_neg_conj                        none
% 1.55/1.02  --large_theory_mode                     true
% 1.55/1.02  --prolific_symb_bound                   200
% 1.55/1.02  --lt_threshold                          2000
% 1.55/1.02  --clause_weak_htbl                      true
% 1.55/1.02  --gc_record_bc_elim                     false
% 1.55/1.02  
% 1.55/1.02  ------ Preprocessing Options
% 1.55/1.02  
% 1.55/1.02  --preprocessing_flag                    true
% 1.55/1.02  --time_out_prep_mult                    0.1
% 1.55/1.02  --splitting_mode                        input
% 1.55/1.02  --splitting_grd                         true
% 1.55/1.02  --splitting_cvd                         false
% 1.55/1.02  --splitting_cvd_svl                     false
% 1.55/1.02  --splitting_nvd                         32
% 1.55/1.02  --sub_typing                            true
% 1.55/1.02  --prep_gs_sim                           true
% 1.55/1.02  --prep_unflatten                        true
% 1.55/1.02  --prep_res_sim                          true
% 1.55/1.02  --prep_upred                            true
% 1.55/1.02  --prep_sem_filter                       exhaustive
% 1.55/1.02  --prep_sem_filter_out                   false
% 1.55/1.02  --pred_elim                             true
% 1.55/1.02  --res_sim_input                         true
% 1.55/1.02  --eq_ax_congr_red                       true
% 1.55/1.02  --pure_diseq_elim                       true
% 1.55/1.02  --brand_transform                       false
% 1.55/1.02  --non_eq_to_eq                          false
% 1.55/1.02  --prep_def_merge                        true
% 1.55/1.02  --prep_def_merge_prop_impl              false
% 1.55/1.02  --prep_def_merge_mbd                    true
% 1.55/1.02  --prep_def_merge_tr_red                 false
% 1.55/1.02  --prep_def_merge_tr_cl                  false
% 1.55/1.02  --smt_preprocessing                     true
% 1.55/1.02  --smt_ac_axioms                         fast
% 1.55/1.02  --preprocessed_out                      false
% 1.55/1.02  --preprocessed_stats                    false
% 1.55/1.02  
% 1.55/1.02  ------ Abstraction refinement Options
% 1.55/1.02  
% 1.55/1.02  --abstr_ref                             []
% 1.55/1.02  --abstr_ref_prep                        false
% 1.55/1.02  --abstr_ref_until_sat                   false
% 1.55/1.02  --abstr_ref_sig_restrict                funpre
% 1.55/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/1.02  --abstr_ref_under                       []
% 1.55/1.02  
% 1.55/1.02  ------ SAT Options
% 1.55/1.02  
% 1.55/1.02  --sat_mode                              false
% 1.55/1.02  --sat_fm_restart_options                ""
% 1.55/1.02  --sat_gr_def                            false
% 1.55/1.02  --sat_epr_types                         true
% 1.55/1.02  --sat_non_cyclic_types                  false
% 1.55/1.02  --sat_finite_models                     false
% 1.55/1.02  --sat_fm_lemmas                         false
% 1.55/1.02  --sat_fm_prep                           false
% 1.55/1.02  --sat_fm_uc_incr                        true
% 1.55/1.02  --sat_out_model                         small
% 1.55/1.02  --sat_out_clauses                       false
% 1.55/1.02  
% 1.55/1.02  ------ QBF Options
% 1.55/1.02  
% 1.55/1.02  --qbf_mode                              false
% 1.55/1.02  --qbf_elim_univ                         false
% 1.55/1.02  --qbf_dom_inst                          none
% 1.55/1.02  --qbf_dom_pre_inst                      false
% 1.55/1.02  --qbf_sk_in                             false
% 1.55/1.02  --qbf_pred_elim                         true
% 1.55/1.02  --qbf_split                             512
% 1.55/1.02  
% 1.55/1.02  ------ BMC1 Options
% 1.55/1.02  
% 1.55/1.02  --bmc1_incremental                      false
% 1.55/1.02  --bmc1_axioms                           reachable_all
% 1.55/1.02  --bmc1_min_bound                        0
% 1.55/1.02  --bmc1_max_bound                        -1
% 1.55/1.02  --bmc1_max_bound_default                -1
% 1.55/1.02  --bmc1_symbol_reachability              true
% 1.55/1.02  --bmc1_property_lemmas                  false
% 1.55/1.02  --bmc1_k_induction                      false
% 1.55/1.02  --bmc1_non_equiv_states                 false
% 1.55/1.02  --bmc1_deadlock                         false
% 1.55/1.02  --bmc1_ucm                              false
% 1.55/1.02  --bmc1_add_unsat_core                   none
% 1.55/1.02  --bmc1_unsat_core_children              false
% 1.55/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/1.02  --bmc1_out_stat                         full
% 1.55/1.02  --bmc1_ground_init                      false
% 1.55/1.02  --bmc1_pre_inst_next_state              false
% 1.55/1.02  --bmc1_pre_inst_state                   false
% 1.55/1.02  --bmc1_pre_inst_reach_state             false
% 1.55/1.02  --bmc1_out_unsat_core                   false
% 1.55/1.02  --bmc1_aig_witness_out                  false
% 1.55/1.02  --bmc1_verbose                          false
% 1.55/1.02  --bmc1_dump_clauses_tptp                false
% 1.55/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.55/1.02  --bmc1_dump_file                        -
% 1.55/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.55/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.55/1.02  --bmc1_ucm_extend_mode                  1
% 1.55/1.02  --bmc1_ucm_init_mode                    2
% 1.55/1.02  --bmc1_ucm_cone_mode                    none
% 1.55/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.55/1.02  --bmc1_ucm_relax_model                  4
% 1.55/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.55/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/1.02  --bmc1_ucm_layered_model                none
% 1.55/1.02  --bmc1_ucm_max_lemma_size               10
% 1.55/1.02  
% 1.55/1.02  ------ AIG Options
% 1.55/1.02  
% 1.55/1.02  --aig_mode                              false
% 1.55/1.02  
% 1.55/1.02  ------ Instantiation Options
% 1.55/1.02  
% 1.55/1.02  --instantiation_flag                    true
% 1.55/1.02  --inst_sos_flag                         false
% 1.55/1.02  --inst_sos_phase                        true
% 1.55/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/1.02  --inst_lit_sel_side                     none
% 1.55/1.02  --inst_solver_per_active                1400
% 1.55/1.02  --inst_solver_calls_frac                1.
% 1.55/1.02  --inst_passive_queue_type               priority_queues
% 1.55/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/1.02  --inst_passive_queues_freq              [25;2]
% 1.55/1.02  --inst_dismatching                      true
% 1.55/1.02  --inst_eager_unprocessed_to_passive     true
% 1.55/1.02  --inst_prop_sim_given                   true
% 1.55/1.02  --inst_prop_sim_new                     false
% 1.55/1.02  --inst_subs_new                         false
% 1.55/1.02  --inst_eq_res_simp                      false
% 1.55/1.02  --inst_subs_given                       false
% 1.55/1.02  --inst_orphan_elimination               true
% 1.55/1.02  --inst_learning_loop_flag               true
% 1.55/1.02  --inst_learning_start                   3000
% 1.55/1.02  --inst_learning_factor                  2
% 1.55/1.02  --inst_start_prop_sim_after_learn       3
% 1.55/1.02  --inst_sel_renew                        solver
% 1.55/1.02  --inst_lit_activity_flag                true
% 1.55/1.02  --inst_restr_to_given                   false
% 1.55/1.02  --inst_activity_threshold               500
% 1.55/1.02  --inst_out_proof                        true
% 1.55/1.02  
% 1.55/1.02  ------ Resolution Options
% 1.55/1.02  
% 1.55/1.02  --resolution_flag                       false
% 1.55/1.02  --res_lit_sel                           adaptive
% 1.55/1.02  --res_lit_sel_side                      none
% 1.55/1.02  --res_ordering                          kbo
% 1.55/1.02  --res_to_prop_solver                    active
% 1.55/1.02  --res_prop_simpl_new                    false
% 1.55/1.02  --res_prop_simpl_given                  true
% 1.55/1.02  --res_passive_queue_type                priority_queues
% 1.55/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/1.02  --res_passive_queues_freq               [15;5]
% 1.55/1.02  --res_forward_subs                      full
% 1.55/1.02  --res_backward_subs                     full
% 1.55/1.02  --res_forward_subs_resolution           true
% 1.55/1.02  --res_backward_subs_resolution          true
% 1.55/1.02  --res_orphan_elimination                true
% 1.55/1.02  --res_time_limit                        2.
% 1.55/1.02  --res_out_proof                         true
% 1.55/1.02  
% 1.55/1.02  ------ Superposition Options
% 1.55/1.02  
% 1.55/1.02  --superposition_flag                    true
% 1.55/1.02  --sup_passive_queue_type                priority_queues
% 1.55/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.55/1.02  --demod_completeness_check              fast
% 1.55/1.02  --demod_use_ground                      true
% 1.55/1.02  --sup_to_prop_solver                    passive
% 1.55/1.02  --sup_prop_simpl_new                    true
% 1.55/1.02  --sup_prop_simpl_given                  true
% 1.55/1.02  --sup_fun_splitting                     false
% 1.55/1.02  --sup_smt_interval                      50000
% 1.55/1.02  
% 1.55/1.02  ------ Superposition Simplification Setup
% 1.55/1.02  
% 1.55/1.02  --sup_indices_passive                   []
% 1.55/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.02  --sup_full_bw                           [BwDemod]
% 1.55/1.02  --sup_immed_triv                        [TrivRules]
% 1.55/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.02  --sup_immed_bw_main                     []
% 1.55/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.02  
% 1.55/1.02  ------ Combination Options
% 1.55/1.02  
% 1.55/1.02  --comb_res_mult                         3
% 1.55/1.02  --comb_sup_mult                         2
% 1.55/1.02  --comb_inst_mult                        10
% 1.55/1.02  
% 1.55/1.02  ------ Debug Options
% 1.55/1.02  
% 1.55/1.02  --dbg_backtrace                         false
% 1.55/1.02  --dbg_dump_prop_clauses                 false
% 1.55/1.02  --dbg_dump_prop_clauses_file            -
% 1.55/1.02  --dbg_out_stat                          false
% 1.55/1.02  
% 1.55/1.02  
% 1.55/1.02  
% 1.55/1.02  
% 1.55/1.02  ------ Proving...
% 1.55/1.02  
% 1.55/1.02  
% 1.55/1.02  % SZS status Theorem for theBenchmark.p
% 1.55/1.02  
% 1.55/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.55/1.02  
% 1.55/1.02  fof(f8,conjecture,(
% 1.55/1.02    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 1.55/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.02  
% 1.55/1.02  fof(f9,negated_conjecture,(
% 1.55/1.02    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 1.55/1.02    inference(negated_conjecture,[],[f8])).
% 1.55/1.02  
% 1.55/1.02  fof(f26,plain,(
% 1.55/1.02    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.55/1.02    inference(ennf_transformation,[],[f9])).
% 1.55/1.02  
% 1.55/1.02  fof(f27,plain,(
% 1.55/1.02    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.55/1.02    inference(flattening,[],[f26])).
% 1.55/1.02  
% 1.55/1.02  fof(f34,plain,(
% 1.55/1.02    ( ! [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) => (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),sK3) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.55/1.02    introduced(choice_axiom,[])).
% 1.55/1.02  
% 1.55/1.02  fof(f33,plain,(
% 1.55/1.02    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),X1) & m1_subset_1(X1,u1_struct_0(sK2))) & l3_lattices(sK2) & v13_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2))),
% 1.55/1.02    introduced(choice_axiom,[])).
% 1.55/1.02  
% 1.55/1.02  fof(f35,plain,(
% 1.55/1.02    (k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & l3_lattices(sK2) & v13_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2)),
% 1.55/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f34,f33])).
% 1.55/1.02  
% 1.55/1.02  fof(f54,plain,(
% 1.55/1.02    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.55/1.02    inference(cnf_transformation,[],[f35])).
% 1.55/1.02  
% 1.55/1.02  fof(f4,axiom,(
% 1.55/1.02    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.55/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.02  
% 1.55/1.02  fof(f19,plain,(
% 1.55/1.02    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.55/1.02    inference(ennf_transformation,[],[f4])).
% 1.55/1.02  
% 1.55/1.02  fof(f45,plain,(
% 1.55/1.02    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f19])).
% 1.55/1.02  
% 1.55/1.02  fof(f3,axiom,(
% 1.55/1.02    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 1.55/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.02  
% 1.55/1.02  fof(f17,plain,(
% 1.55/1.02    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.55/1.02    inference(ennf_transformation,[],[f3])).
% 1.55/1.02  
% 1.55/1.02  fof(f18,plain,(
% 1.55/1.02    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.55/1.02    inference(flattening,[],[f17])).
% 1.55/1.02  
% 1.55/1.02  fof(f44,plain,(
% 1.55/1.02    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f18])).
% 1.55/1.02  
% 1.55/1.02  fof(f50,plain,(
% 1.55/1.02    ~v2_struct_0(sK2)),
% 1.55/1.02    inference(cnf_transformation,[],[f35])).
% 1.55/1.02  
% 1.55/1.02  fof(f53,plain,(
% 1.55/1.02    l3_lattices(sK2)),
% 1.55/1.02    inference(cnf_transformation,[],[f35])).
% 1.55/1.02  
% 1.55/1.02  fof(f1,axiom,(
% 1.55/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.55/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.02  
% 1.55/1.02  fof(f10,plain,(
% 1.55/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.55/1.02    inference(pure_predicate_removal,[],[f1])).
% 1.55/1.02  
% 1.55/1.02  fof(f11,plain,(
% 1.55/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.55/1.02    inference(pure_predicate_removal,[],[f10])).
% 1.55/1.02  
% 1.55/1.02  fof(f12,plain,(
% 1.55/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.55/1.02    inference(pure_predicate_removal,[],[f11])).
% 1.55/1.02  
% 1.55/1.02  fof(f13,plain,(
% 1.55/1.02    ! [X0] : (((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.55/1.02    inference(ennf_transformation,[],[f12])).
% 1.55/1.02  
% 1.55/1.02  fof(f14,plain,(
% 1.55/1.02    ! [X0] : ((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.55/1.02    inference(flattening,[],[f13])).
% 1.55/1.02  
% 1.55/1.02  fof(f37,plain,(
% 1.55/1.02    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f14])).
% 1.55/1.02  
% 1.55/1.02  fof(f46,plain,(
% 1.55/1.02    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f19])).
% 1.55/1.02  
% 1.55/1.02  fof(f5,axiom,(
% 1.55/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 1.55/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.02  
% 1.55/1.02  fof(f20,plain,(
% 1.55/1.02    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.55/1.02    inference(ennf_transformation,[],[f5])).
% 1.55/1.02  
% 1.55/1.02  fof(f21,plain,(
% 1.55/1.02    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.55/1.02    inference(flattening,[],[f20])).
% 1.55/1.02  
% 1.55/1.02  fof(f47,plain,(
% 1.55/1.02    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f21])).
% 1.55/1.02  
% 1.55/1.02  fof(f51,plain,(
% 1.55/1.02    v10_lattices(sK2)),
% 1.55/1.02    inference(cnf_transformation,[],[f35])).
% 1.55/1.02  
% 1.55/1.02  fof(f7,axiom,(
% 1.55/1.02    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 1.55/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.02  
% 1.55/1.02  fof(f24,plain,(
% 1.55/1.02    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.55/1.02    inference(ennf_transformation,[],[f7])).
% 1.55/1.02  
% 1.55/1.02  fof(f25,plain,(
% 1.55/1.02    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.55/1.02    inference(flattening,[],[f24])).
% 1.55/1.02  
% 1.55/1.02  fof(f49,plain,(
% 1.55/1.02    ( ! [X0,X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f25])).
% 1.55/1.02  
% 1.55/1.02  fof(f52,plain,(
% 1.55/1.02    v13_lattices(sK2)),
% 1.55/1.02    inference(cnf_transformation,[],[f35])).
% 1.55/1.02  
% 1.55/1.02  fof(f38,plain,(
% 1.55/1.02    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f14])).
% 1.55/1.02  
% 1.55/1.02  fof(f6,axiom,(
% 1.55/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 1.55/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.02  
% 1.55/1.02  fof(f22,plain,(
% 1.55/1.02    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.55/1.02    inference(ennf_transformation,[],[f6])).
% 1.55/1.02  
% 1.55/1.02  fof(f23,plain,(
% 1.55/1.02    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.55/1.02    inference(flattening,[],[f22])).
% 1.55/1.02  
% 1.55/1.02  fof(f48,plain,(
% 1.55/1.02    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f23])).
% 1.55/1.02  
% 1.55/1.02  fof(f2,axiom,(
% 1.55/1.02    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 1.55/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.02  
% 1.55/1.02  fof(f15,plain,(
% 1.55/1.02    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.55/1.02    inference(ennf_transformation,[],[f2])).
% 1.55/1.02  
% 1.55/1.02  fof(f16,plain,(
% 1.55/1.02    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.55/1.02    inference(flattening,[],[f15])).
% 1.55/1.02  
% 1.55/1.02  fof(f28,plain,(
% 1.55/1.02    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.55/1.02    inference(nnf_transformation,[],[f16])).
% 1.55/1.02  
% 1.55/1.02  fof(f29,plain,(
% 1.55/1.02    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.55/1.02    inference(rectify,[],[f28])).
% 1.55/1.02  
% 1.55/1.02  fof(f31,plain,(
% 1.55/1.02    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK1(X0))) != X1 & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 1.55/1.02    introduced(choice_axiom,[])).
% 1.55/1.02  
% 1.55/1.02  fof(f30,plain,(
% 1.55/1.02    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK0(X0),k1_lattices(X0,sK0(X0),X2)) != sK0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 1.55/1.02    introduced(choice_axiom,[])).
% 1.55/1.02  
% 1.55/1.02  fof(f32,plain,(
% 1.55/1.02    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK0(X0),k1_lattices(X0,sK0(X0),sK1(X0))) != sK0(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.55/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 1.55/1.02  
% 1.55/1.02  fof(f40,plain,(
% 1.55/1.02    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f32])).
% 1.55/1.02  
% 1.55/1.02  fof(f39,plain,(
% 1.55/1.02    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.55/1.02    inference(cnf_transformation,[],[f14])).
% 1.55/1.02  
% 1.55/1.02  fof(f55,plain,(
% 1.55/1.02    k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),sK3)),
% 1.55/1.02    inference(cnf_transformation,[],[f35])).
% 1.55/1.02  
% 1.55/1.02  cnf(c_15,negated_conjecture,
% 1.55/1.02      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.55/1.02      inference(cnf_transformation,[],[f54]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_505,negated_conjecture,
% 1.55/1.02      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.55/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_627,plain,
% 1.55/1.02      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.55/1.02      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_10,plain,
% 1.55/1.02      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 1.55/1.02      inference(cnf_transformation,[],[f45]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_8,plain,
% 1.55/1.02      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 1.55/1.02      | ~ l1_lattices(X0)
% 1.55/1.02      | v2_struct_0(X0) ),
% 1.55/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_297,plain,
% 1.55/1.02      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 1.55/1.02      | ~ l3_lattices(X0)
% 1.55/1.02      | v2_struct_0(X0) ),
% 1.55/1.02      inference(resolution,[status(thm)],[c_10,c_8]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_19,negated_conjecture,
% 1.55/1.02      ( ~ v2_struct_0(sK2) ),
% 1.55/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_409,plain,
% 1.55/1.02      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 1.55/1.02      | ~ l3_lattices(X0)
% 1.55/1.02      | sK2 != X0 ),
% 1.55/1.02      inference(resolution_lifted,[status(thm)],[c_297,c_19]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_410,plain,
% 1.55/1.02      ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
% 1.55/1.02      | ~ l3_lattices(sK2) ),
% 1.55/1.02      inference(unflattening,[status(thm)],[c_409]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_16,negated_conjecture,
% 1.55/1.02      ( l3_lattices(sK2) ),
% 1.55/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_35,plain,
% 1.55/1.02      ( l1_lattices(sK2) | ~ l3_lattices(sK2) ),
% 1.55/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_41,plain,
% 1.55/1.02      ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
% 1.55/1.02      | ~ l1_lattices(sK2)
% 1.55/1.02      | v2_struct_0(sK2) ),
% 1.55/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_412,plain,
% 1.55/1.02      ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2)) ),
% 1.55/1.02      inference(global_propositional_subsumption,
% 1.55/1.02                [status(thm)],
% 1.55/1.02                [c_410,c_19,c_16,c_35,c_41]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_501,plain,
% 1.55/1.02      ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2)) ),
% 1.55/1.02      inference(subtyping,[status(esa)],[c_412]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_631,plain,
% 1.55/1.02      ( m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2)) = iProver_top ),
% 1.55/1.02      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_2,plain,
% 1.55/1.02      ( v4_lattices(X0)
% 1.55/1.02      | ~ l3_lattices(X0)
% 1.55/1.02      | v2_struct_0(X0)
% 1.55/1.02      | ~ v10_lattices(X0) ),
% 1.55/1.02      inference(cnf_transformation,[],[f37]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_9,plain,
% 1.55/1.02      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 1.55/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_11,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.02      | ~ l2_lattices(X1)
% 1.55/1.02      | ~ v4_lattices(X1)
% 1.55/1.02      | v2_struct_0(X1)
% 1.55/1.02      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 1.55/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_230,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.02      | ~ v4_lattices(X1)
% 1.55/1.02      | ~ l3_lattices(X3)
% 1.55/1.02      | v2_struct_0(X1)
% 1.55/1.02      | X1 != X3
% 1.55/1.02      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 1.55/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_231,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.02      | ~ v4_lattices(X1)
% 1.55/1.02      | ~ l3_lattices(X1)
% 1.55/1.02      | v2_struct_0(X1)
% 1.55/1.02      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 1.55/1.02      inference(unflattening,[status(thm)],[c_230]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_315,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.02      | ~ l3_lattices(X3)
% 1.55/1.02      | ~ l3_lattices(X1)
% 1.55/1.02      | v2_struct_0(X3)
% 1.55/1.02      | v2_struct_0(X1)
% 1.55/1.02      | ~ v10_lattices(X3)
% 1.55/1.02      | X1 != X3
% 1.55/1.02      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 1.55/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_231]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_316,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.02      | ~ l3_lattices(X1)
% 1.55/1.02      | v2_struct_0(X1)
% 1.55/1.02      | ~ v10_lattices(X1)
% 1.55/1.02      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 1.55/1.02      inference(unflattening,[status(thm)],[c_315]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_18,negated_conjecture,
% 1.55/1.02      ( v10_lattices(sK2) ),
% 1.55/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_357,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.02      | ~ l3_lattices(X1)
% 1.55/1.02      | v2_struct_0(X1)
% 1.55/1.02      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0)
% 1.55/1.02      | sK2 != X1 ),
% 1.55/1.02      inference(resolution_lifted,[status(thm)],[c_316,c_18]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_358,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.55/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.55/1.02      | ~ l3_lattices(sK2)
% 1.55/1.02      | v2_struct_0(sK2)
% 1.55/1.02      | k3_lattices(sK2,X1,X0) = k1_lattices(sK2,X1,X0) ),
% 1.55/1.02      inference(unflattening,[status(thm)],[c_357]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_362,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.55/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.55/1.02      | k3_lattices(sK2,X1,X0) = k1_lattices(sK2,X1,X0) ),
% 1.55/1.02      inference(global_propositional_subsumption,
% 1.55/1.02                [status(thm)],
% 1.55/1.02                [c_358,c_19,c_16]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_503,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.55/1.02      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 1.55/1.02      | k3_lattices(sK2,X1_48,X0_48) = k1_lattices(sK2,X1_48,X0_48) ),
% 1.55/1.02      inference(subtyping,[status(esa)],[c_362]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_629,plain,
% 1.55/1.02      ( k3_lattices(sK2,X0_48,X1_48) = k1_lattices(sK2,X0_48,X1_48)
% 1.55/1.02      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
% 1.55/1.02      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.55/1.02      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_748,plain,
% 1.55/1.02      ( k3_lattices(sK2,k5_lattices(sK2),X0_48) = k1_lattices(sK2,k5_lattices(sK2),X0_48)
% 1.55/1.02      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.55/1.02      inference(superposition,[status(thm)],[c_631,c_629]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_1228,plain,
% 1.55/1.02      ( k3_lattices(sK2,k5_lattices(sK2),sK3) = k1_lattices(sK2,k5_lattices(sK2),sK3) ),
% 1.55/1.02      inference(superposition,[status(thm)],[c_627,c_748]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_13,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.02      | ~ v13_lattices(X1)
% 1.55/1.02      | ~ l3_lattices(X1)
% 1.55/1.02      | v2_struct_0(X1)
% 1.55/1.02      | ~ v10_lattices(X1)
% 1.55/1.02      | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
% 1.55/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_17,negated_conjecture,
% 1.55/1.02      ( v13_lattices(sK2) ),
% 1.55/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_209,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.02      | ~ l3_lattices(X1)
% 1.55/1.02      | v2_struct_0(X1)
% 1.55/1.02      | ~ v10_lattices(X1)
% 1.55/1.02      | k3_lattices(X1,k5_lattices(X1),X0) = X0
% 1.55/1.02      | sK2 != X1 ),
% 1.55/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_210,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.55/1.02      | ~ l3_lattices(sK2)
% 1.55/1.02      | v2_struct_0(sK2)
% 1.55/1.02      | ~ v10_lattices(sK2)
% 1.55/1.02      | k3_lattices(sK2,k5_lattices(sK2),X0) = X0 ),
% 1.55/1.02      inference(unflattening,[status(thm)],[c_209]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_214,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.55/1.02      | k3_lattices(sK2,k5_lattices(sK2),X0) = X0 ),
% 1.55/1.02      inference(global_propositional_subsumption,
% 1.55/1.02                [status(thm)],
% 1.55/1.02                [c_210,c_19,c_18,c_16]) ).
% 1.55/1.02  
% 1.55/1.02  cnf(c_504,plain,
% 1.55/1.02      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.55/1.02      | k3_lattices(sK2,k5_lattices(sK2),X0_48) = X0_48 ),
% 1.55/1.03      inference(subtyping,[status(esa)],[c_214]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_628,plain,
% 1.55/1.03      ( k3_lattices(sK2,k5_lattices(sK2),X0_48) = X0_48
% 1.55/1.03      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.55/1.03      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_700,plain,
% 1.55/1.03      ( k3_lattices(sK2,k5_lattices(sK2),sK3) = sK3 ),
% 1.55/1.03      inference(superposition,[status(thm)],[c_627,c_628]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_1234,plain,
% 1.55/1.03      ( k1_lattices(sK2,k5_lattices(sK2),sK3) = sK3 ),
% 1.55/1.03      inference(light_normalisation,[status(thm)],[c_1228,c_700]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_510,plain,
% 1.55/1.03      ( X0_48 != X1_48
% 1.55/1.03      | k2_lattices(X0_50,X2_48,X0_48) = k2_lattices(X0_50,X2_48,X1_48) ),
% 1.55/1.03      theory(equality) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_1139,plain,
% 1.55/1.03      ( k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) = k2_lattices(sK2,k5_lattices(sK2),X1_48)
% 1.55/1.03      | k1_lattices(sK2,k5_lattices(sK2),X0_48) != X1_48 ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_510]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_1141,plain,
% 1.55/1.03      ( k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) = k2_lattices(sK2,k5_lattices(sK2),sK3)
% 1.55/1.03      | k1_lattices(sK2,k5_lattices(sK2),sK3) != sK3 ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_1139]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_509,plain,
% 1.55/1.03      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 1.55/1.03      theory(equality) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_797,plain,
% 1.55/1.03      ( k4_lattices(sK2,k5_lattices(sK2),sK3) != X0_48
% 1.55/1.03      | k4_lattices(sK2,k5_lattices(sK2),sK3) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X1_48))
% 1.55/1.03      | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X1_48)) != X0_48 ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_509]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_1018,plain,
% 1.55/1.03      ( k4_lattices(sK2,k5_lattices(sK2),sK3) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48))
% 1.55/1.03      | k4_lattices(sK2,k5_lattices(sK2),sK3) != k2_lattices(sK2,k5_lattices(sK2),sK3)
% 1.55/1.03      | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) != k2_lattices(sK2,k5_lattices(sK2),sK3) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_797]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_1019,plain,
% 1.55/1.03      ( k4_lattices(sK2,k5_lattices(sK2),sK3) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3))
% 1.55/1.03      | k4_lattices(sK2,k5_lattices(sK2),sK3) != k2_lattices(sK2,k5_lattices(sK2),sK3)
% 1.55/1.03      | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) != k2_lattices(sK2,k5_lattices(sK2),sK3) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_1018]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_1,plain,
% 1.55/1.03      ( v6_lattices(X0)
% 1.55/1.03      | ~ l3_lattices(X0)
% 1.55/1.03      | v2_struct_0(X0)
% 1.55/1.03      | ~ v10_lattices(X0) ),
% 1.55/1.03      inference(cnf_transformation,[],[f38]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_12,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.03      | ~ l1_lattices(X1)
% 1.55/1.03      | ~ v6_lattices(X1)
% 1.55/1.03      | v2_struct_0(X1)
% 1.55/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 1.55/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_261,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.03      | ~ l1_lattices(X1)
% 1.55/1.03      | ~ l3_lattices(X3)
% 1.55/1.03      | v2_struct_0(X3)
% 1.55/1.03      | v2_struct_0(X1)
% 1.55/1.03      | ~ v10_lattices(X3)
% 1.55/1.03      | X1 != X3
% 1.55/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 1.55/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_12]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_262,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.03      | ~ l1_lattices(X1)
% 1.55/1.03      | ~ l3_lattices(X1)
% 1.55/1.03      | v2_struct_0(X1)
% 1.55/1.03      | ~ v10_lattices(X1)
% 1.55/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 1.55/1.03      inference(unflattening,[status(thm)],[c_261]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_280,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.03      | ~ l3_lattices(X1)
% 1.55/1.03      | v2_struct_0(X1)
% 1.55/1.03      | ~ v10_lattices(X1)
% 1.55/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 1.55/1.03      inference(forward_subsumption_resolution,
% 1.55/1.03                [status(thm)],
% 1.55/1.03                [c_262,c_10]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_378,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.03      | ~ l3_lattices(X1)
% 1.55/1.03      | v2_struct_0(X1)
% 1.55/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0)
% 1.55/1.03      | sK2 != X1 ),
% 1.55/1.03      inference(resolution_lifted,[status(thm)],[c_280,c_18]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_379,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.55/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.55/1.03      | ~ l3_lattices(sK2)
% 1.55/1.03      | v2_struct_0(sK2)
% 1.55/1.03      | k4_lattices(sK2,X1,X0) = k2_lattices(sK2,X1,X0) ),
% 1.55/1.03      inference(unflattening,[status(thm)],[c_378]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_383,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.55/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.55/1.03      | k4_lattices(sK2,X1,X0) = k2_lattices(sK2,X1,X0) ),
% 1.55/1.03      inference(global_propositional_subsumption,
% 1.55/1.03                [status(thm)],
% 1.55/1.03                [c_379,c_19,c_16]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_502,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.55/1.03      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 1.55/1.03      | k4_lattices(sK2,X1_48,X0_48) = k2_lattices(sK2,X1_48,X0_48) ),
% 1.55/1.03      inference(subtyping,[status(esa)],[c_383]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_821,plain,
% 1.55/1.03      ( ~ m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
% 1.55/1.03      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.55/1.03      | k4_lattices(sK2,k5_lattices(sK2),sK3) = k2_lattices(sK2,k5_lattices(sK2),sK3) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_502]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_674,plain,
% 1.55/1.03      ( k4_lattices(sK2,k5_lattices(sK2),sK3) != X0_48
% 1.55/1.03      | k5_lattices(sK2) != X0_48
% 1.55/1.03      | k5_lattices(sK2) = k4_lattices(sK2,k5_lattices(sK2),sK3) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_509]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_763,plain,
% 1.55/1.03      ( k4_lattices(sK2,k5_lattices(sK2),sK3) != k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48))
% 1.55/1.03      | k5_lattices(sK2) = k4_lattices(sK2,k5_lattices(sK2),sK3)
% 1.55/1.03      | k5_lattices(sK2) != k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_674]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_764,plain,
% 1.55/1.03      ( k4_lattices(sK2,k5_lattices(sK2),sK3) != k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3))
% 1.55/1.03      | k5_lattices(sK2) = k4_lattices(sK2,k5_lattices(sK2),sK3)
% 1.55/1.03      | k5_lattices(sK2) != k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_763]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_7,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.03      | ~ l3_lattices(X1)
% 1.55/1.03      | v2_struct_0(X1)
% 1.55/1.03      | ~ v9_lattices(X1)
% 1.55/1.03      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 1.55/1.03      inference(cnf_transformation,[],[f40]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_426,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.55/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.55/1.03      | ~ l3_lattices(X1)
% 1.55/1.03      | ~ v9_lattices(X1)
% 1.55/1.03      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 1.55/1.03      | sK2 != X1 ),
% 1.55/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_427,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.55/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.55/1.03      | ~ l3_lattices(sK2)
% 1.55/1.03      | ~ v9_lattices(sK2)
% 1.55/1.03      | k2_lattices(sK2,X1,k1_lattices(sK2,X1,X0)) = X1 ),
% 1.55/1.03      inference(unflattening,[status(thm)],[c_426]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_0,plain,
% 1.55/1.03      ( ~ l3_lattices(X0)
% 1.55/1.03      | v2_struct_0(X0)
% 1.55/1.03      | ~ v10_lattices(X0)
% 1.55/1.03      | v9_lattices(X0) ),
% 1.55/1.03      inference(cnf_transformation,[],[f39]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_63,plain,
% 1.55/1.03      ( ~ l3_lattices(sK2)
% 1.55/1.03      | v2_struct_0(sK2)
% 1.55/1.03      | ~ v10_lattices(sK2)
% 1.55/1.03      | v9_lattices(sK2) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_431,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.55/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.55/1.03      | k2_lattices(sK2,X1,k1_lattices(sK2,X1,X0)) = X1 ),
% 1.55/1.03      inference(global_propositional_subsumption,
% 1.55/1.03                [status(thm)],
% 1.55/1.03                [c_427,c_19,c_18,c_16,c_63]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_500,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.55/1.03      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 1.55/1.03      | k2_lattices(sK2,X1_48,k1_lattices(sK2,X1_48,X0_48)) = X1_48 ),
% 1.55/1.03      inference(subtyping,[status(esa)],[c_431]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_716,plain,
% 1.55/1.03      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.55/1.03      | ~ m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
% 1.55/1.03      | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) = k5_lattices(sK2) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_500]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_719,plain,
% 1.55/1.03      ( ~ m1_subset_1(k5_lattices(sK2),u1_struct_0(sK2))
% 1.55/1.03      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.55/1.03      | k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) = k5_lattices(sK2) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_716]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_687,plain,
% 1.55/1.03      ( X0_48 != X1_48
% 1.55/1.03      | k5_lattices(sK2) != X1_48
% 1.55/1.03      | k5_lattices(sK2) = X0_48 ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_509]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_709,plain,
% 1.55/1.03      ( X0_48 != k5_lattices(sK2)
% 1.55/1.03      | k5_lattices(sK2) = X0_48
% 1.55/1.03      | k5_lattices(sK2) != k5_lattices(sK2) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_687]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_715,plain,
% 1.55/1.03      ( k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48)) != k5_lattices(sK2)
% 1.55/1.03      | k5_lattices(sK2) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),X0_48))
% 1.55/1.03      | k5_lattices(sK2) != k5_lattices(sK2) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_709]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_717,plain,
% 1.55/1.03      ( k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3)) != k5_lattices(sK2)
% 1.55/1.03      | k5_lattices(sK2) = k2_lattices(sK2,k5_lattices(sK2),k1_lattices(sK2,k5_lattices(sK2),sK3))
% 1.55/1.03      | k5_lattices(sK2) != k5_lattices(sK2) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_715]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_508,plain,( X0_48 = X0_48 ),theory(equality) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_686,plain,
% 1.55/1.03      ( k5_lattices(sK2) = k5_lattices(sK2) ),
% 1.55/1.03      inference(instantiation,[status(thm)],[c_508]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_14,negated_conjecture,
% 1.55/1.03      ( k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),sK3) ),
% 1.55/1.03      inference(cnf_transformation,[],[f55]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(c_506,negated_conjecture,
% 1.55/1.03      ( k5_lattices(sK2) != k4_lattices(sK2,k5_lattices(sK2),sK3) ),
% 1.55/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 1.55/1.03  
% 1.55/1.03  cnf(contradiction,plain,
% 1.55/1.03      ( $false ),
% 1.55/1.03      inference(minisat,
% 1.55/1.03                [status(thm)],
% 1.55/1.03                [c_1234,c_1141,c_1019,c_821,c_764,c_719,c_717,c_686,
% 1.55/1.03                 c_506,c_41,c_35,c_15,c_16,c_19]) ).
% 1.55/1.03  
% 1.55/1.03  
% 1.55/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.55/1.03  
% 1.55/1.03  ------                               Statistics
% 1.55/1.03  
% 1.55/1.03  ------ General
% 1.55/1.03  
% 1.55/1.03  abstr_ref_over_cycles:                  0
% 1.55/1.03  abstr_ref_under_cycles:                 0
% 1.55/1.03  gc_basic_clause_elim:                   0
% 1.55/1.03  forced_gc_time:                         0
% 1.55/1.03  parsing_time:                           0.012
% 1.55/1.03  unif_index_cands_time:                  0.
% 1.55/1.03  unif_index_add_time:                    0.
% 1.55/1.03  orderings_time:                         0.
% 1.55/1.03  out_proof_time:                         0.013
% 1.55/1.03  total_time:                             0.077
% 1.55/1.03  num_of_symbols:                         51
% 1.55/1.03  num_of_terms:                           1170
% 1.55/1.03  
% 1.55/1.03  ------ Preprocessing
% 1.55/1.03  
% 1.55/1.03  num_of_splits:                          0
% 1.55/1.03  num_of_split_atoms:                     0
% 1.55/1.03  num_of_reused_defs:                     0
% 1.55/1.03  num_eq_ax_congr_red:                    26
% 1.55/1.03  num_of_sem_filtered_clauses:            1
% 1.55/1.03  num_of_subtypes:                        3
% 1.55/1.03  monotx_restored_types:                  0
% 1.55/1.03  sat_num_of_epr_types:                   0
% 1.55/1.03  sat_num_of_non_cyclic_types:            0
% 1.55/1.03  sat_guarded_non_collapsed_types:        1
% 1.55/1.03  num_pure_diseq_elim:                    0
% 1.55/1.03  simp_replaced_by:                       0
% 1.55/1.03  res_preprocessed:                       53
% 1.55/1.03  prep_upred:                             0
% 1.55/1.03  prep_unflattend:                        12
% 1.55/1.03  smt_new_axioms:                         0
% 1.55/1.03  pred_elim_cands:                        1
% 1.55/1.03  pred_elim:                              9
% 1.55/1.03  pred_elim_cl:                           12
% 1.55/1.03  pred_elim_cycles:                       11
% 1.55/1.03  merged_defs:                            0
% 1.55/1.03  merged_defs_ncl:                        0
% 1.55/1.03  bin_hyper_res:                          0
% 1.55/1.03  prep_cycles:                            4
% 1.55/1.03  pred_elim_time:                         0.004
% 1.55/1.03  splitting_time:                         0.
% 1.55/1.03  sem_filter_time:                        0.
% 1.55/1.03  monotx_time:                            0.
% 1.55/1.03  subtype_inf_time:                       0.
% 1.55/1.03  
% 1.55/1.03  ------ Problem properties
% 1.55/1.03  
% 1.55/1.03  clauses:                                7
% 1.55/1.03  conjectures:                            2
% 1.55/1.03  epr:                                    0
% 1.55/1.03  horn:                                   7
% 1.55/1.03  ground:                                 3
% 1.55/1.03  unary:                                  3
% 1.55/1.03  binary:                                 1
% 1.55/1.03  lits:                                   14
% 1.55/1.03  lits_eq:                                5
% 1.55/1.03  fd_pure:                                0
% 1.55/1.03  fd_pseudo:                              0
% 1.55/1.03  fd_cond:                                0
% 1.55/1.03  fd_pseudo_cond:                         0
% 1.55/1.03  ac_symbols:                             0
% 1.55/1.03  
% 1.55/1.03  ------ Propositional Solver
% 1.55/1.03  
% 1.55/1.03  prop_solver_calls:                      28
% 1.55/1.03  prop_fast_solver_calls:                 354
% 1.55/1.03  smt_solver_calls:                       0
% 1.55/1.03  smt_fast_solver_calls:                  0
% 1.55/1.03  prop_num_of_clauses:                    433
% 1.55/1.03  prop_preprocess_simplified:             1632
% 1.55/1.03  prop_fo_subsumed:                       12
% 1.55/1.03  prop_solver_time:                       0.
% 1.55/1.03  smt_solver_time:                        0.
% 1.55/1.03  smt_fast_solver_time:                   0.
% 1.55/1.03  prop_fast_solver_time:                  0.
% 1.55/1.03  prop_unsat_core_time:                   0.
% 1.55/1.03  
% 1.55/1.03  ------ QBF
% 1.55/1.03  
% 1.55/1.03  qbf_q_res:                              0
% 1.55/1.03  qbf_num_tautologies:                    0
% 1.55/1.03  qbf_prep_cycles:                        0
% 1.55/1.03  
% 1.55/1.03  ------ BMC1
% 1.55/1.03  
% 1.55/1.03  bmc1_current_bound:                     -1
% 1.55/1.03  bmc1_last_solved_bound:                 -1
% 1.55/1.03  bmc1_unsat_core_size:                   -1
% 1.55/1.03  bmc1_unsat_core_parents_size:           -1
% 1.55/1.03  bmc1_merge_next_fun:                    0
% 1.55/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.55/1.03  
% 1.55/1.03  ------ Instantiation
% 1.55/1.03  
% 1.55/1.03  inst_num_of_clauses:                    143
% 1.55/1.03  inst_num_in_passive:                    36
% 1.55/1.03  inst_num_in_active:                     86
% 1.55/1.03  inst_num_in_unprocessed:                21
% 1.55/1.03  inst_num_of_loops:                      100
% 1.55/1.03  inst_num_of_learning_restarts:          0
% 1.55/1.03  inst_num_moves_active_passive:          8
% 1.55/1.03  inst_lit_activity:                      0
% 1.55/1.03  inst_lit_activity_moves:                0
% 1.55/1.03  inst_num_tautologies:                   0
% 1.55/1.03  inst_num_prop_implied:                  0
% 1.55/1.03  inst_num_existing_simplified:           0
% 1.55/1.03  inst_num_eq_res_simplified:             0
% 1.55/1.03  inst_num_child_elim:                    0
% 1.55/1.03  inst_num_of_dismatching_blockings:      21
% 1.55/1.03  inst_num_of_non_proper_insts:           125
% 1.55/1.03  inst_num_of_duplicates:                 0
% 1.55/1.03  inst_inst_num_from_inst_to_res:         0
% 1.55/1.03  inst_dismatching_checking_time:         0.
% 1.55/1.03  
% 1.55/1.03  ------ Resolution
% 1.55/1.03  
% 1.55/1.03  res_num_of_clauses:                     0
% 1.55/1.03  res_num_in_passive:                     0
% 1.55/1.03  res_num_in_active:                      0
% 1.55/1.03  res_num_of_loops:                       57
% 1.55/1.03  res_forward_subset_subsumed:            18
% 1.55/1.03  res_backward_subset_subsumed:           0
% 1.55/1.03  res_forward_subsumed:                   0
% 1.55/1.03  res_backward_subsumed:                  0
% 1.55/1.03  res_forward_subsumption_resolution:     1
% 1.55/1.03  res_backward_subsumption_resolution:    0
% 1.55/1.03  res_clause_to_clause_subsumption:       32
% 1.55/1.03  res_orphan_elimination:                 0
% 1.55/1.03  res_tautology_del:                      16
% 1.55/1.03  res_num_eq_res_simplified:              0
% 1.55/1.03  res_num_sel_changes:                    0
% 1.55/1.03  res_moves_from_active_to_pass:          0
% 1.55/1.03  
% 1.55/1.03  ------ Superposition
% 1.55/1.03  
% 1.55/1.03  sup_time_total:                         0.
% 1.55/1.03  sup_time_generating:                    0.
% 1.55/1.03  sup_time_sim_full:                      0.
% 1.55/1.03  sup_time_sim_immed:                     0.
% 1.55/1.03  
% 1.55/1.03  sup_num_of_clauses:                     23
% 1.55/1.03  sup_num_in_active:                      19
% 1.55/1.03  sup_num_in_passive:                     4
% 1.55/1.03  sup_num_of_loops:                       18
% 1.55/1.03  sup_fw_superposition:                   16
% 1.55/1.03  sup_bw_superposition:                   0
% 1.55/1.03  sup_immediate_simplified:               2
% 1.55/1.03  sup_given_eliminated:                   0
% 1.55/1.03  comparisons_done:                       0
% 1.55/1.03  comparisons_avoided:                    0
% 1.55/1.03  
% 1.55/1.03  ------ Simplifications
% 1.55/1.03  
% 1.55/1.03  
% 1.55/1.03  sim_fw_subset_subsumed:                 0
% 1.55/1.03  sim_bw_subset_subsumed:                 0
% 1.55/1.03  sim_fw_subsumed:                        0
% 1.55/1.03  sim_bw_subsumed:                        0
% 1.55/1.03  sim_fw_subsumption_res:                 0
% 1.55/1.03  sim_bw_subsumption_res:                 0
% 1.55/1.03  sim_tautology_del:                      0
% 1.55/1.03  sim_eq_tautology_del:                   0
% 1.55/1.03  sim_eq_res_simp:                        0
% 1.55/1.03  sim_fw_demodulated:                     0
% 1.55/1.03  sim_bw_demodulated:                     0
% 1.55/1.03  sim_light_normalised:                   2
% 1.55/1.03  sim_joinable_taut:                      0
% 1.55/1.03  sim_joinable_simp:                      0
% 1.55/1.03  sim_ac_normalised:                      0
% 1.55/1.03  sim_smt_subsumption:                    0
% 1.55/1.03  
%------------------------------------------------------------------------------
