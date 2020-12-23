%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1208+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:09 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 431 expanded)
%              Number of clauses        :   66 ( 110 expanded)
%              Number of leaves         :   15 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          :  513 (2144 expanded)
%              Number of equality atoms :  134 ( 385 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k4_lattices(X0,k6_lattices(X0),sK4) != sK4
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_lattices(X0,k6_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k4_lattices(sK3,k6_lattices(sK3),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v14_lattices(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k4_lattices(sK3,k6_lattices(sK3),sK4) != sK4
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v14_lattices(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f39,f38])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK2(X0))) != X1
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f49,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f40])).

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
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK0(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK0(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK0(X0,X1)) != X1 )
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X0,X3] :
      ( k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f59,plain,(
    v14_lattices(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    k4_lattices(sK3,k6_lattices(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_533,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1323,plain,
    ( k2_lattices(sK3,sK4,k6_lattices(sK3)) != X0_47
    | sK4 != X0_47
    | sK4 = k2_lattices(sK3,sK4,k6_lattices(sK3)) ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_1324,plain,
    ( k2_lattices(sK3,sK4,k6_lattices(sK3)) != sK4
    | sK4 = k2_lattices(sK3,sK4,k6_lattices(sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_778,plain,
    ( k4_lattices(sK3,k6_lattices(sK3),sK4) != X0_47
    | k4_lattices(sK3,k6_lattices(sK3),sK4) = sK4
    | sK4 != X0_47 ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_1029,plain,
    ( k4_lattices(sK3,k6_lattices(sK3),sK4) != k2_lattices(sK3,sK4,k6_lattices(sK3))
    | k4_lattices(sK3,k6_lattices(sK3),sK4) = sK4
    | sK4 != k2_lattices(sK3,sK4,k6_lattices(sK3)) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_12,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_442,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_443,plain,
    ( m1_subset_1(k6_lattices(sK3),u1_struct_0(sK3))
    | ~ l2_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_18,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_13,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_34,plain,
    ( l2_lattices(sK3)
    | ~ l3_lattices(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_37,plain,
    ( m1_subset_1(k6_lattices(sK3),u1_struct_0(sK3))
    | ~ l2_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_445,plain,
    ( m1_subset_1(k6_lattices(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_21,c_18,c_34,c_37])).

cnf(c_521,plain,
    ( m1_subset_1(k6_lattices(sK3),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_709,plain,
    ( m1_subset_1(k6_lattices(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_529,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_701,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v9_lattices(sK3)
    | k2_lattices(sK3,X1,k1_lattices(sK3,X1,X0)) = X1 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_20,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_71,plain,
    ( ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3)
    | v9_lattices(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k2_lattices(sK3,X1,k1_lattices(sK3,X1,X0)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_21,c_20,c_18,c_71])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK3))
    | k2_lattices(sK3,X1_47,k1_lattices(sK3,X1_47,X0_47)) = X1_47 ),
    inference(subtyping,[status(esa)],[c_324])).

cnf(c_704,plain,
    ( k2_lattices(sK3,X0_47,k1_lattices(sK3,X0_47,X1_47)) = X0_47
    | m1_subset_1(X1_47,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_929,plain,
    ( k2_lattices(sK3,sK4,k1_lattices(sK3,sK4,X0_47)) = sK4
    | m1_subset_1(X0_47,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_704])).

cnf(c_1018,plain,
    ( k2_lattices(sK3,sK4,k1_lattices(sK3,sK4,k6_lattices(sK3))) = sK4 ),
    inference(superposition,[status(thm)],[c_709,c_929])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v14_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,negated_conjecture,
    ( v14_lattices(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k6_lattices(sK3),u1_struct_0(sK3))
    | ~ l2_lattices(sK3)
    | v2_struct_0(sK3)
    | k1_lattices(sK3,X0,k6_lattices(sK3)) = k6_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k1_lattices(sK3,X0,k6_lattices(sK3)) = k6_lattices(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_21,c_18,c_34,c_37])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK3))
    | k1_lattices(sK3,X0_47,k6_lattices(sK3)) = k6_lattices(sK3) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_706,plain,
    ( k1_lattices(sK3,X0_47,k6_lattices(sK3)) = k6_lattices(sK3)
    | m1_subset_1(X0_47,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_836,plain,
    ( k1_lattices(sK3,sK4,k6_lattices(sK3)) = k6_lattices(sK3) ),
    inference(superposition,[status(thm)],[c_701,c_706])).

cnf(c_1020,plain,
    ( k2_lattices(sK3,sK4,k6_lattices(sK3)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_1018,c_836])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_230,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_231,plain,
    ( v6_lattices(sK3)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_68,plain,
    ( v6_lattices(sK3)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_233,plain,
    ( v6_lattices(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_231,c_21,c_20,c_18,c_68])).

cnf(c_256,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_233])).

cnf(c_257,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_lattices(sK3)
    | v2_struct_0(sK3)
    | k2_lattices(sK3,X0,X1) = k4_lattices(sK3,X0,X1) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_14,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,plain,
    ( l1_lattices(sK3)
    | ~ l3_lattices(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k2_lattices(sK3,X0,X1) = k4_lattices(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_257,c_21,c_18,c_31])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK3))
    | k2_lattices(sK3,X0_47,X1_47) = k4_lattices(sK3,X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_261])).

cnf(c_877,plain,
    ( ~ m1_subset_1(k6_lattices(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k2_lattices(sK3,sK4,k6_lattices(sK3)) = k4_lattices(sK3,sK4,k6_lattices(sK3)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_791,plain,
    ( X0_47 != X1_47
    | k4_lattices(sK3,k6_lattices(sK3),sK4) != X1_47
    | k4_lattices(sK3,k6_lattices(sK3),sK4) = X0_47 ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_823,plain,
    ( X0_47 != k4_lattices(sK3,sK4,k6_lattices(sK3))
    | k4_lattices(sK3,k6_lattices(sK3),sK4) = X0_47
    | k4_lattices(sK3,k6_lattices(sK3),sK4) != k4_lattices(sK3,sK4,k6_lattices(sK3)) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_876,plain,
    ( k2_lattices(sK3,sK4,k6_lattices(sK3)) != k4_lattices(sK3,sK4,k6_lattices(sK3))
    | k4_lattices(sK3,k6_lattices(sK3),sK4) = k2_lattices(sK3,sK4,k6_lattices(sK3))
    | k4_lattices(sK3,k6_lattices(sK3),sK4) != k4_lattices(sK3,sK4,k6_lattices(sK3)) ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_233])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_lattices(sK3)
    | v2_struct_0(sK3)
    | k4_lattices(sK3,X0,X1) = k4_lattices(sK3,X1,X0) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_lattices(sK3,X0,X1) = k4_lattices(sK3,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_278,c_21,c_18,c_31])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK3))
    | k4_lattices(sK3,X0_47,X1_47) = k4_lattices(sK3,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_282])).

cnf(c_786,plain,
    ( ~ m1_subset_1(k6_lattices(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_lattices(sK3,k6_lattices(sK3),sK4) = k4_lattices(sK3,sK4,k6_lattices(sK3)) ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_16,negated_conjecture,
    ( k4_lattices(sK3,k6_lattices(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_530,negated_conjecture,
    ( k4_lattices(sK3,k6_lattices(sK3),sK4) != sK4 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_532,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_543,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1324,c_1029,c_1020,c_877,c_876,c_786,c_530,c_543,c_37,c_34,c_17,c_18,c_21])).


%------------------------------------------------------------------------------
