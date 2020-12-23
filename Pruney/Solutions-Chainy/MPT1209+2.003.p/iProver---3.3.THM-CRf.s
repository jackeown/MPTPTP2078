%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:20 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 859 expanded)
%              Number of clauses        :  104 ( 225 expanded)
%              Number of leaves         :   16 ( 217 expanded)
%              Depth                    :   23
%              Number of atoms          :  670 (4202 expanded)
%              Number of equality atoms :  164 ( 719 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k6_lattices(X0),X1) != k6_lattices(X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k6_lattices(X0),X1) != k6_lattices(X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k6_lattices(X0),X1) != k6_lattices(X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k3_lattices(X0,k6_lattices(X0),sK3) != k6_lattices(X0)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_lattices(X0,k6_lattices(X0),X1) != k6_lattices(X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k3_lattices(sK2,k6_lattices(sK2),X1) != k6_lattices(sK2)
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l3_lattices(sK2)
      & v14_lattices(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k3_lattices(sK2,k6_lattices(sK2),sK3) != k6_lattices(sK2)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v14_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f41,f40])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    v14_lattices(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f45,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f39,plain,(
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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK1(X0)) != sK1(X0)
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f49,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    k3_lattices(sK2,k6_lattices(sK2),sK3) != k6_lattices(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_616,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_756,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( v14_lattices(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k6_lattices(X1),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | k4_lattices(sK2,k6_lattices(sK2),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k4_lattices(sK2,k6_lattices(sK2),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_22,c_21,c_19])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | k4_lattices(sK2,k6_lattices(sK2),X0_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_247])).

cnf(c_757,plain,
    ( k4_lattices(sK2,k6_lattices(sK2),X0_49) = X0_49
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_846,plain,
    ( k4_lattices(sK2,k6_lattices(sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_756,c_757])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_263,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_2,c_15])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_1])).

cnf(c_268,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_267])).

cnf(c_299,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_268,c_21])).

cnf(c_300,plain,
    ( r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_304,plain,
    ( r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_22,c_19])).

cnf(c_14,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_342,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_343,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | v9_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_75,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | v9_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_345,plain,
    ( v9_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_22,c_21,c_19,c_75])).

cnf(c_431,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_345])).

cnf(c_432,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k2_lattices(sK2,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_72,plain,
    ( v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r1_lattices(sK2,X0,X1)
    | k2_lattices(sK2,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_22,c_21,c_19,c_72])).

cnf(c_437,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_436])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | X3 != X0
    | k4_lattices(sK2,X0,X1) != X2
    | k2_lattices(sK2,X2,X3) = X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_304,c_437])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k4_lattices(sK2,X0,X1),u1_struct_0(sK2))
    | k2_lattices(sK2,k4_lattices(sK2,X0,X1),X0) = k4_lattices(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | ~ m1_subset_1(k4_lattices(sK2,X0_49,X1_49),u1_struct_0(sK2))
    | k2_lattices(sK2,k4_lattices(sK2,X0_49,X1_49),X0_49) = k4_lattices(sK2,X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_491])).

cnf(c_760,plain,
    ( k2_lattices(sK2,k4_lattices(sK2,X0_49,X1_49),X0_49) = k4_lattices(sK2,X0_49,X1_49)
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k4_lattices(sK2,X0_49,X1_49),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_1689,plain,
    ( k2_lattices(sK2,k4_lattices(sK2,k6_lattices(sK2),sK3),k6_lattices(sK2)) = k4_lattices(sK2,k6_lattices(sK2),sK3)
    | m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_760])).

cnf(c_1699,plain,
    ( k2_lattices(sK2,sK3,k6_lattices(sK2)) = sK3
    | m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1689,c_846])).

cnf(c_23,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,plain,
    ( l3_lattices(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_43,plain,
    ( l2_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_45,plain,
    ( l2_lattices(sK2) = iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_10,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_46,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) = iProver_top
    | l2_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_48,plain,
    ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) = iProver_top
    | l2_lattices(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_1969,plain,
    ( k2_lattices(sK2,sK3,k6_lattices(sK2)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1699,c_23,c_26,c_27,c_45,c_48])).

cnf(c_413,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_10])).

cnf(c_513,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_413,c_22])).

cnf(c_514,plain,
    ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2))
    | ~ l3_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_44,plain,
    ( l2_lattices(sK2)
    | ~ l3_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_47,plain,
    ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_516,plain,
    ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_22,c_19,c_44,c_47])).

cnf(c_611,plain,
    ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_516])).

cnf(c_761,plain,
    ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | k1_lattices(sK2,k2_lattices(sK2,X1,X0),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X1,X0),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_22,c_21,c_19,c_72])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X1_49,X0_49),X0_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_535])).

cnf(c_762,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,X0_49,X1_49),X1_49) = X1_49
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_905,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,X0_49),X0_49) = X0_49
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_762])).

cnf(c_963,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,k6_lattices(sK2)),k6_lattices(sK2)) = k6_lattices(sK2) ),
    inference(superposition,[status(thm)],[c_761,c_905])).

cnf(c_1972,plain,
    ( k1_lattices(sK2,sK3,k6_lattices(sK2)) = k6_lattices(sK2) ),
    inference(demodulation,[status(thm)],[c_1969,c_963])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_320,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_321,plain,
    ( v4_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_66,plain,
    ( v4_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_323,plain,
    ( v4_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_22,c_21,c_19,c_66])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_323])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | v2_struct_0(sK2)
    | k1_lattices(sK2,X1,X0) = k3_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,X1,X0) = k3_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_22,c_19,c_44])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | k1_lattices(sK2,X1_49,X0_49) = k3_lattices(sK2,X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_368])).

cnf(c_758,plain,
    ( k1_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X0_49,X1_49)
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_1007,plain,
    ( k1_lattices(sK2,sK3,X0_49) = k3_lattices(sK2,sK3,X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_758])).

cnf(c_1025,plain,
    ( k1_lattices(sK2,sK3,k6_lattices(sK2)) = k3_lattices(sK2,sK3,k6_lattices(sK2)) ),
    inference(superposition,[status(thm)],[c_761,c_1007])).

cnf(c_2084,plain,
    ( k3_lattices(sK2,sK3,k6_lattices(sK2)) = k6_lattices(sK2) ),
    inference(demodulation,[status(thm)],[c_1972,c_1025])).

cnf(c_620,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_926,plain,
    ( X0_49 != X1_49
    | k4_lattices(sK2,X2_49,X3_49) != X1_49
    | k4_lattices(sK2,X2_49,X3_49) = X0_49 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_989,plain,
    ( X0_49 != X1_49
    | k4_lattices(sK2,k6_lattices(sK2),X1_49) != X1_49
    | k4_lattices(sK2,k6_lattices(sK2),X1_49) = X0_49 ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_1444,plain,
    ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) = k3_lattices(sK2,sK3,k6_lattices(sK2))
    | k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) != k6_lattices(sK2)
    | k3_lattices(sK2,sK3,k6_lattices(sK2)) != k6_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_323])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | v2_struct_0(sK2)
    | k3_lattices(sK2,X1,X0) = k3_lattices(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k3_lattices(sK2,X1,X0) = k3_lattices(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_22,c_19,c_44])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | k3_lattices(sK2,X1_49,X0_49) = k3_lattices(sK2,X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_1074,plain,
    ( ~ m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k3_lattices(sK2,k6_lattices(sK2),sK3) = k3_lattices(sK2,sK3,k6_lattices(sK2)) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_1001,plain,
    ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) != X0_49
    | k3_lattices(sK2,k6_lattices(sK2),sK3) != X0_49
    | k3_lattices(sK2,k6_lattices(sK2),sK3) = k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_1073,plain,
    ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) != k3_lattices(sK2,sK3,k6_lattices(sK2))
    | k3_lattices(sK2,k6_lattices(sK2),sK3) = k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2))
    | k3_lattices(sK2,k6_lattices(sK2),sK3) != k3_lattices(sK2,sK3,k6_lattices(sK2)) ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_814,plain,
    ( k3_lattices(sK2,k6_lattices(sK2),sK3) != X0_49
    | k3_lattices(sK2,k6_lattices(sK2),sK3) = k6_lattices(sK2)
    | k6_lattices(sK2) != X0_49 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_969,plain,
    ( k3_lattices(sK2,k6_lattices(sK2),sK3) != k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2))
    | k3_lattices(sK2,k6_lattices(sK2),sK3) = k6_lattices(sK2)
    | k6_lattices(sK2) != k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_826,plain,
    ( X0_49 != X1_49
    | k6_lattices(sK2) != X1_49
    | k6_lattices(sK2) = X0_49 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_852,plain,
    ( X0_49 != k6_lattices(sK2)
    | k6_lattices(sK2) = X0_49
    | k6_lattices(sK2) != k6_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_919,plain,
    ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) != k6_lattices(sK2)
    | k6_lattices(sK2) = k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2))
    | k6_lattices(sK2) != k6_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_619,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_853,plain,
    ( k6_lattices(sK2) = k6_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_847,plain,
    ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) = k6_lattices(sK2) ),
    inference(superposition,[status(thm)],[c_761,c_757])).

cnf(c_17,negated_conjecture,
    ( k3_lattices(sK2,k6_lattices(sK2),sK3) != k6_lattices(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_617,negated_conjecture,
    ( k3_lattices(sK2,k6_lattices(sK2),sK3) != k6_lattices(sK2) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2084,c_1444,c_1074,c_1073,c_969,c_919,c_853,c_847,c_617,c_47,c_44,c_18,c_19,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:42:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.86/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/0.99  
% 1.86/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.86/0.99  
% 1.86/0.99  ------  iProver source info
% 1.86/0.99  
% 1.86/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.86/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.86/0.99  git: non_committed_changes: false
% 1.86/0.99  git: last_make_outside_of_git: false
% 1.86/0.99  
% 1.86/0.99  ------ 
% 1.86/0.99  
% 1.86/0.99  ------ Input Options
% 1.86/0.99  
% 1.86/0.99  --out_options                           all
% 1.86/0.99  --tptp_safe_out                         true
% 1.86/0.99  --problem_path                          ""
% 1.86/0.99  --include_path                          ""
% 1.86/0.99  --clausifier                            res/vclausify_rel
% 1.86/0.99  --clausifier_options                    --mode clausify
% 1.86/0.99  --stdin                                 false
% 1.86/0.99  --stats_out                             all
% 1.86/0.99  
% 1.86/0.99  ------ General Options
% 1.86/0.99  
% 1.86/0.99  --fof                                   false
% 1.86/0.99  --time_out_real                         305.
% 1.86/0.99  --time_out_virtual                      -1.
% 1.86/0.99  --symbol_type_check                     false
% 1.86/0.99  --clausify_out                          false
% 1.86/0.99  --sig_cnt_out                           false
% 1.86/0.99  --trig_cnt_out                          false
% 1.86/0.99  --trig_cnt_out_tolerance                1.
% 1.86/0.99  --trig_cnt_out_sk_spl                   false
% 1.86/0.99  --abstr_cl_out                          false
% 1.86/0.99  
% 1.86/0.99  ------ Global Options
% 1.86/0.99  
% 1.86/0.99  --schedule                              default
% 1.86/0.99  --add_important_lit                     false
% 1.86/0.99  --prop_solver_per_cl                    1000
% 1.86/0.99  --min_unsat_core                        false
% 1.86/0.99  --soft_assumptions                      false
% 1.86/0.99  --soft_lemma_size                       3
% 1.86/0.99  --prop_impl_unit_size                   0
% 1.86/0.99  --prop_impl_unit                        []
% 1.86/0.99  --share_sel_clauses                     true
% 1.86/0.99  --reset_solvers                         false
% 1.86/0.99  --bc_imp_inh                            [conj_cone]
% 1.86/0.99  --conj_cone_tolerance                   3.
% 1.86/0.99  --extra_neg_conj                        none
% 1.86/0.99  --large_theory_mode                     true
% 1.86/0.99  --prolific_symb_bound                   200
% 1.86/0.99  --lt_threshold                          2000
% 1.86/0.99  --clause_weak_htbl                      true
% 1.86/0.99  --gc_record_bc_elim                     false
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing Options
% 1.86/0.99  
% 1.86/0.99  --preprocessing_flag                    true
% 1.86/0.99  --time_out_prep_mult                    0.1
% 1.86/0.99  --splitting_mode                        input
% 1.86/0.99  --splitting_grd                         true
% 1.86/0.99  --splitting_cvd                         false
% 1.86/0.99  --splitting_cvd_svl                     false
% 1.86/0.99  --splitting_nvd                         32
% 1.86/0.99  --sub_typing                            true
% 1.86/0.99  --prep_gs_sim                           true
% 1.86/0.99  --prep_unflatten                        true
% 1.86/0.99  --prep_res_sim                          true
% 1.86/0.99  --prep_upred                            true
% 1.86/0.99  --prep_sem_filter                       exhaustive
% 1.86/0.99  --prep_sem_filter_out                   false
% 1.86/0.99  --pred_elim                             true
% 1.86/0.99  --res_sim_input                         true
% 1.86/0.99  --eq_ax_congr_red                       true
% 1.86/0.99  --pure_diseq_elim                       true
% 1.86/0.99  --brand_transform                       false
% 1.86/0.99  --non_eq_to_eq                          false
% 1.86/0.99  --prep_def_merge                        true
% 1.86/0.99  --prep_def_merge_prop_impl              false
% 1.86/0.99  --prep_def_merge_mbd                    true
% 1.86/0.99  --prep_def_merge_tr_red                 false
% 1.86/0.99  --prep_def_merge_tr_cl                  false
% 1.86/0.99  --smt_preprocessing                     true
% 1.86/0.99  --smt_ac_axioms                         fast
% 1.86/0.99  --preprocessed_out                      false
% 1.86/0.99  --preprocessed_stats                    false
% 1.86/0.99  
% 1.86/0.99  ------ Abstraction refinement Options
% 1.86/0.99  
% 1.86/0.99  --abstr_ref                             []
% 1.86/0.99  --abstr_ref_prep                        false
% 1.86/0.99  --abstr_ref_until_sat                   false
% 1.86/0.99  --abstr_ref_sig_restrict                funpre
% 1.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.86/0.99  --abstr_ref_under                       []
% 1.86/0.99  
% 1.86/0.99  ------ SAT Options
% 1.86/0.99  
% 1.86/0.99  --sat_mode                              false
% 1.86/0.99  --sat_fm_restart_options                ""
% 1.86/0.99  --sat_gr_def                            false
% 1.86/0.99  --sat_epr_types                         true
% 1.86/0.99  --sat_non_cyclic_types                  false
% 1.86/0.99  --sat_finite_models                     false
% 1.86/0.99  --sat_fm_lemmas                         false
% 1.86/0.99  --sat_fm_prep                           false
% 1.86/0.99  --sat_fm_uc_incr                        true
% 1.86/0.99  --sat_out_model                         small
% 1.86/0.99  --sat_out_clauses                       false
% 1.86/0.99  
% 1.86/0.99  ------ QBF Options
% 1.86/0.99  
% 1.86/0.99  --qbf_mode                              false
% 1.86/0.99  --qbf_elim_univ                         false
% 1.86/0.99  --qbf_dom_inst                          none
% 1.86/0.99  --qbf_dom_pre_inst                      false
% 1.86/0.99  --qbf_sk_in                             false
% 1.86/0.99  --qbf_pred_elim                         true
% 1.86/0.99  --qbf_split                             512
% 1.86/0.99  
% 1.86/0.99  ------ BMC1 Options
% 1.86/0.99  
% 1.86/0.99  --bmc1_incremental                      false
% 1.86/0.99  --bmc1_axioms                           reachable_all
% 1.86/0.99  --bmc1_min_bound                        0
% 1.86/0.99  --bmc1_max_bound                        -1
% 1.86/0.99  --bmc1_max_bound_default                -1
% 1.86/0.99  --bmc1_symbol_reachability              true
% 1.86/0.99  --bmc1_property_lemmas                  false
% 1.86/0.99  --bmc1_k_induction                      false
% 1.86/0.99  --bmc1_non_equiv_states                 false
% 1.86/0.99  --bmc1_deadlock                         false
% 1.86/0.99  --bmc1_ucm                              false
% 1.86/0.99  --bmc1_add_unsat_core                   none
% 1.86/0.99  --bmc1_unsat_core_children              false
% 1.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.86/0.99  --bmc1_out_stat                         full
% 1.86/0.99  --bmc1_ground_init                      false
% 1.86/0.99  --bmc1_pre_inst_next_state              false
% 1.86/0.99  --bmc1_pre_inst_state                   false
% 1.86/0.99  --bmc1_pre_inst_reach_state             false
% 1.86/0.99  --bmc1_out_unsat_core                   false
% 1.86/0.99  --bmc1_aig_witness_out                  false
% 1.86/0.99  --bmc1_verbose                          false
% 1.86/0.99  --bmc1_dump_clauses_tptp                false
% 1.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.86/0.99  --bmc1_dump_file                        -
% 1.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.86/0.99  --bmc1_ucm_extend_mode                  1
% 1.86/0.99  --bmc1_ucm_init_mode                    2
% 1.86/0.99  --bmc1_ucm_cone_mode                    none
% 1.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.86/0.99  --bmc1_ucm_relax_model                  4
% 1.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.86/0.99  --bmc1_ucm_layered_model                none
% 1.86/0.99  --bmc1_ucm_max_lemma_size               10
% 1.86/0.99  
% 1.86/0.99  ------ AIG Options
% 1.86/0.99  
% 1.86/0.99  --aig_mode                              false
% 1.86/0.99  
% 1.86/0.99  ------ Instantiation Options
% 1.86/0.99  
% 1.86/0.99  --instantiation_flag                    true
% 1.86/0.99  --inst_sos_flag                         false
% 1.86/0.99  --inst_sos_phase                        true
% 1.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.86/0.99  --inst_lit_sel_side                     num_symb
% 1.86/0.99  --inst_solver_per_active                1400
% 1.86/0.99  --inst_solver_calls_frac                1.
% 1.86/0.99  --inst_passive_queue_type               priority_queues
% 1.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.86/0.99  --inst_passive_queues_freq              [25;2]
% 1.86/0.99  --inst_dismatching                      true
% 1.86/0.99  --inst_eager_unprocessed_to_passive     true
% 1.86/0.99  --inst_prop_sim_given                   true
% 1.86/0.99  --inst_prop_sim_new                     false
% 1.86/0.99  --inst_subs_new                         false
% 1.86/0.99  --inst_eq_res_simp                      false
% 1.86/0.99  --inst_subs_given                       false
% 1.86/0.99  --inst_orphan_elimination               true
% 1.86/0.99  --inst_learning_loop_flag               true
% 1.86/0.99  --inst_learning_start                   3000
% 1.86/0.99  --inst_learning_factor                  2
% 1.86/0.99  --inst_start_prop_sim_after_learn       3
% 1.86/0.99  --inst_sel_renew                        solver
% 1.86/0.99  --inst_lit_activity_flag                true
% 1.86/0.99  --inst_restr_to_given                   false
% 1.86/0.99  --inst_activity_threshold               500
% 1.86/0.99  --inst_out_proof                        true
% 1.86/0.99  
% 1.86/0.99  ------ Resolution Options
% 1.86/0.99  
% 1.86/0.99  --resolution_flag                       true
% 1.86/0.99  --res_lit_sel                           adaptive
% 1.86/0.99  --res_lit_sel_side                      none
% 1.86/0.99  --res_ordering                          kbo
% 1.86/0.99  --res_to_prop_solver                    active
% 1.86/0.99  --res_prop_simpl_new                    false
% 1.86/0.99  --res_prop_simpl_given                  true
% 1.86/0.99  --res_passive_queue_type                priority_queues
% 1.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.86/0.99  --res_passive_queues_freq               [15;5]
% 1.86/0.99  --res_forward_subs                      full
% 1.86/0.99  --res_backward_subs                     full
% 1.86/0.99  --res_forward_subs_resolution           true
% 1.86/0.99  --res_backward_subs_resolution          true
% 1.86/0.99  --res_orphan_elimination                true
% 1.86/0.99  --res_time_limit                        2.
% 1.86/0.99  --res_out_proof                         true
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Options
% 1.86/0.99  
% 1.86/0.99  --superposition_flag                    true
% 1.86/0.99  --sup_passive_queue_type                priority_queues
% 1.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.86/0.99  --demod_completeness_check              fast
% 1.86/0.99  --demod_use_ground                      true
% 1.86/0.99  --sup_to_prop_solver                    passive
% 1.86/0.99  --sup_prop_simpl_new                    true
% 1.86/0.99  --sup_prop_simpl_given                  true
% 1.86/0.99  --sup_fun_splitting                     false
% 1.86/0.99  --sup_smt_interval                      50000
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Simplification Setup
% 1.86/0.99  
% 1.86/0.99  --sup_indices_passive                   []
% 1.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_full_bw                           [BwDemod]
% 1.86/0.99  --sup_immed_triv                        [TrivRules]
% 1.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_immed_bw_main                     []
% 1.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  
% 1.86/0.99  ------ Combination Options
% 1.86/0.99  
% 1.86/0.99  --comb_res_mult                         3
% 1.86/0.99  --comb_sup_mult                         2
% 1.86/0.99  --comb_inst_mult                        10
% 1.86/0.99  
% 1.86/0.99  ------ Debug Options
% 1.86/0.99  
% 1.86/0.99  --dbg_backtrace                         false
% 1.86/0.99  --dbg_dump_prop_clauses                 false
% 1.86/0.99  --dbg_dump_prop_clauses_file            -
% 1.86/0.99  --dbg_out_stat                          false
% 1.86/0.99  ------ Parsing...
% 1.86/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.86/0.99  ------ Proving...
% 1.86/0.99  ------ Problem Properties 
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  clauses                                 8
% 1.86/0.99  conjectures                             2
% 1.86/0.99  EPR                                     0
% 1.86/0.99  Horn                                    8
% 1.86/0.99  unary                                   3
% 1.86/0.99  binary                                  1
% 1.86/0.99  lits                                    18
% 1.86/0.99  lits eq                                 6
% 1.86/0.99  fd_pure                                 0
% 1.86/0.99  fd_pseudo                               0
% 1.86/0.99  fd_cond                                 0
% 1.86/0.99  fd_pseudo_cond                          0
% 1.86/0.99  AC symbols                              0
% 1.86/0.99  
% 1.86/0.99  ------ Schedule dynamic 5 is on 
% 1.86/0.99  
% 1.86/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  ------ 
% 1.86/0.99  Current options:
% 1.86/0.99  ------ 
% 1.86/0.99  
% 1.86/0.99  ------ Input Options
% 1.86/0.99  
% 1.86/0.99  --out_options                           all
% 1.86/0.99  --tptp_safe_out                         true
% 1.86/0.99  --problem_path                          ""
% 1.86/0.99  --include_path                          ""
% 1.86/0.99  --clausifier                            res/vclausify_rel
% 1.86/0.99  --clausifier_options                    --mode clausify
% 1.86/0.99  --stdin                                 false
% 1.86/0.99  --stats_out                             all
% 1.86/0.99  
% 1.86/0.99  ------ General Options
% 1.86/0.99  
% 1.86/0.99  --fof                                   false
% 1.86/0.99  --time_out_real                         305.
% 1.86/0.99  --time_out_virtual                      -1.
% 1.86/0.99  --symbol_type_check                     false
% 1.86/0.99  --clausify_out                          false
% 1.86/0.99  --sig_cnt_out                           false
% 1.86/0.99  --trig_cnt_out                          false
% 1.86/0.99  --trig_cnt_out_tolerance                1.
% 1.86/0.99  --trig_cnt_out_sk_spl                   false
% 1.86/0.99  --abstr_cl_out                          false
% 1.86/0.99  
% 1.86/0.99  ------ Global Options
% 1.86/0.99  
% 1.86/0.99  --schedule                              default
% 1.86/0.99  --add_important_lit                     false
% 1.86/0.99  --prop_solver_per_cl                    1000
% 1.86/0.99  --min_unsat_core                        false
% 1.86/0.99  --soft_assumptions                      false
% 1.86/0.99  --soft_lemma_size                       3
% 1.86/0.99  --prop_impl_unit_size                   0
% 1.86/0.99  --prop_impl_unit                        []
% 1.86/0.99  --share_sel_clauses                     true
% 1.86/0.99  --reset_solvers                         false
% 1.86/0.99  --bc_imp_inh                            [conj_cone]
% 1.86/0.99  --conj_cone_tolerance                   3.
% 1.86/0.99  --extra_neg_conj                        none
% 1.86/0.99  --large_theory_mode                     true
% 1.86/0.99  --prolific_symb_bound                   200
% 1.86/0.99  --lt_threshold                          2000
% 1.86/0.99  --clause_weak_htbl                      true
% 1.86/0.99  --gc_record_bc_elim                     false
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing Options
% 1.86/0.99  
% 1.86/0.99  --preprocessing_flag                    true
% 1.86/0.99  --time_out_prep_mult                    0.1
% 1.86/0.99  --splitting_mode                        input
% 1.86/0.99  --splitting_grd                         true
% 1.86/0.99  --splitting_cvd                         false
% 1.86/0.99  --splitting_cvd_svl                     false
% 1.86/0.99  --splitting_nvd                         32
% 1.86/0.99  --sub_typing                            true
% 1.86/0.99  --prep_gs_sim                           true
% 1.86/0.99  --prep_unflatten                        true
% 1.86/0.99  --prep_res_sim                          true
% 1.86/0.99  --prep_upred                            true
% 1.86/0.99  --prep_sem_filter                       exhaustive
% 1.86/0.99  --prep_sem_filter_out                   false
% 1.86/0.99  --pred_elim                             true
% 1.86/0.99  --res_sim_input                         true
% 1.86/0.99  --eq_ax_congr_red                       true
% 1.86/0.99  --pure_diseq_elim                       true
% 1.86/0.99  --brand_transform                       false
% 1.86/0.99  --non_eq_to_eq                          false
% 1.86/0.99  --prep_def_merge                        true
% 1.86/0.99  --prep_def_merge_prop_impl              false
% 1.86/0.99  --prep_def_merge_mbd                    true
% 1.86/0.99  --prep_def_merge_tr_red                 false
% 1.86/0.99  --prep_def_merge_tr_cl                  false
% 1.86/0.99  --smt_preprocessing                     true
% 1.86/0.99  --smt_ac_axioms                         fast
% 1.86/0.99  --preprocessed_out                      false
% 1.86/0.99  --preprocessed_stats                    false
% 1.86/0.99  
% 1.86/0.99  ------ Abstraction refinement Options
% 1.86/0.99  
% 1.86/0.99  --abstr_ref                             []
% 1.86/0.99  --abstr_ref_prep                        false
% 1.86/0.99  --abstr_ref_until_sat                   false
% 1.86/0.99  --abstr_ref_sig_restrict                funpre
% 1.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.86/0.99  --abstr_ref_under                       []
% 1.86/0.99  
% 1.86/0.99  ------ SAT Options
% 1.86/0.99  
% 1.86/0.99  --sat_mode                              false
% 1.86/0.99  --sat_fm_restart_options                ""
% 1.86/0.99  --sat_gr_def                            false
% 1.86/0.99  --sat_epr_types                         true
% 1.86/0.99  --sat_non_cyclic_types                  false
% 1.86/0.99  --sat_finite_models                     false
% 1.86/0.99  --sat_fm_lemmas                         false
% 1.86/0.99  --sat_fm_prep                           false
% 1.86/0.99  --sat_fm_uc_incr                        true
% 1.86/0.99  --sat_out_model                         small
% 1.86/0.99  --sat_out_clauses                       false
% 1.86/0.99  
% 1.86/0.99  ------ QBF Options
% 1.86/0.99  
% 1.86/0.99  --qbf_mode                              false
% 1.86/0.99  --qbf_elim_univ                         false
% 1.86/0.99  --qbf_dom_inst                          none
% 1.86/0.99  --qbf_dom_pre_inst                      false
% 1.86/0.99  --qbf_sk_in                             false
% 1.86/0.99  --qbf_pred_elim                         true
% 1.86/0.99  --qbf_split                             512
% 1.86/0.99  
% 1.86/0.99  ------ BMC1 Options
% 1.86/0.99  
% 1.86/0.99  --bmc1_incremental                      false
% 1.86/0.99  --bmc1_axioms                           reachable_all
% 1.86/0.99  --bmc1_min_bound                        0
% 1.86/0.99  --bmc1_max_bound                        -1
% 1.86/0.99  --bmc1_max_bound_default                -1
% 1.86/0.99  --bmc1_symbol_reachability              true
% 1.86/0.99  --bmc1_property_lemmas                  false
% 1.86/0.99  --bmc1_k_induction                      false
% 1.86/0.99  --bmc1_non_equiv_states                 false
% 1.86/0.99  --bmc1_deadlock                         false
% 1.86/0.99  --bmc1_ucm                              false
% 1.86/0.99  --bmc1_add_unsat_core                   none
% 1.86/0.99  --bmc1_unsat_core_children              false
% 1.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.86/0.99  --bmc1_out_stat                         full
% 1.86/0.99  --bmc1_ground_init                      false
% 1.86/0.99  --bmc1_pre_inst_next_state              false
% 1.86/0.99  --bmc1_pre_inst_state                   false
% 1.86/0.99  --bmc1_pre_inst_reach_state             false
% 1.86/0.99  --bmc1_out_unsat_core                   false
% 1.86/0.99  --bmc1_aig_witness_out                  false
% 1.86/0.99  --bmc1_verbose                          false
% 1.86/0.99  --bmc1_dump_clauses_tptp                false
% 1.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.86/0.99  --bmc1_dump_file                        -
% 1.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.86/0.99  --bmc1_ucm_extend_mode                  1
% 1.86/0.99  --bmc1_ucm_init_mode                    2
% 1.86/0.99  --bmc1_ucm_cone_mode                    none
% 1.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.86/0.99  --bmc1_ucm_relax_model                  4
% 1.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.86/0.99  --bmc1_ucm_layered_model                none
% 1.86/0.99  --bmc1_ucm_max_lemma_size               10
% 1.86/0.99  
% 1.86/0.99  ------ AIG Options
% 1.86/0.99  
% 1.86/0.99  --aig_mode                              false
% 1.86/0.99  
% 1.86/0.99  ------ Instantiation Options
% 1.86/0.99  
% 1.86/0.99  --instantiation_flag                    true
% 1.86/0.99  --inst_sos_flag                         false
% 1.86/0.99  --inst_sos_phase                        true
% 1.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.86/0.99  --inst_lit_sel_side                     none
% 1.86/0.99  --inst_solver_per_active                1400
% 1.86/0.99  --inst_solver_calls_frac                1.
% 1.86/0.99  --inst_passive_queue_type               priority_queues
% 1.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.86/0.99  --inst_passive_queues_freq              [25;2]
% 1.86/0.99  --inst_dismatching                      true
% 1.86/0.99  --inst_eager_unprocessed_to_passive     true
% 1.86/0.99  --inst_prop_sim_given                   true
% 1.86/0.99  --inst_prop_sim_new                     false
% 1.86/0.99  --inst_subs_new                         false
% 1.86/0.99  --inst_eq_res_simp                      false
% 1.86/0.99  --inst_subs_given                       false
% 1.86/0.99  --inst_orphan_elimination               true
% 1.86/0.99  --inst_learning_loop_flag               true
% 1.86/0.99  --inst_learning_start                   3000
% 1.86/0.99  --inst_learning_factor                  2
% 1.86/0.99  --inst_start_prop_sim_after_learn       3
% 1.86/0.99  --inst_sel_renew                        solver
% 1.86/0.99  --inst_lit_activity_flag                true
% 1.86/0.99  --inst_restr_to_given                   false
% 1.86/0.99  --inst_activity_threshold               500
% 1.86/0.99  --inst_out_proof                        true
% 1.86/0.99  
% 1.86/0.99  ------ Resolution Options
% 1.86/0.99  
% 1.86/0.99  --resolution_flag                       false
% 1.86/0.99  --res_lit_sel                           adaptive
% 1.86/0.99  --res_lit_sel_side                      none
% 1.86/0.99  --res_ordering                          kbo
% 1.86/0.99  --res_to_prop_solver                    active
% 1.86/0.99  --res_prop_simpl_new                    false
% 1.86/0.99  --res_prop_simpl_given                  true
% 1.86/0.99  --res_passive_queue_type                priority_queues
% 1.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.86/0.99  --res_passive_queues_freq               [15;5]
% 1.86/0.99  --res_forward_subs                      full
% 1.86/0.99  --res_backward_subs                     full
% 1.86/0.99  --res_forward_subs_resolution           true
% 1.86/0.99  --res_backward_subs_resolution          true
% 1.86/0.99  --res_orphan_elimination                true
% 1.86/0.99  --res_time_limit                        2.
% 1.86/0.99  --res_out_proof                         true
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Options
% 1.86/0.99  
% 1.86/0.99  --superposition_flag                    true
% 1.86/0.99  --sup_passive_queue_type                priority_queues
% 1.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.86/0.99  --demod_completeness_check              fast
% 1.86/0.99  --demod_use_ground                      true
% 1.86/0.99  --sup_to_prop_solver                    passive
% 1.86/0.99  --sup_prop_simpl_new                    true
% 1.86/0.99  --sup_prop_simpl_given                  true
% 1.86/0.99  --sup_fun_splitting                     false
% 1.86/0.99  --sup_smt_interval                      50000
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Simplification Setup
% 1.86/0.99  
% 1.86/0.99  --sup_indices_passive                   []
% 1.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_full_bw                           [BwDemod]
% 1.86/0.99  --sup_immed_triv                        [TrivRules]
% 1.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_immed_bw_main                     []
% 1.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  
% 1.86/0.99  ------ Combination Options
% 1.86/0.99  
% 1.86/0.99  --comb_res_mult                         3
% 1.86/0.99  --comb_sup_mult                         2
% 1.86/0.99  --comb_inst_mult                        10
% 1.86/0.99  
% 1.86/0.99  ------ Debug Options
% 1.86/0.99  
% 1.86/0.99  --dbg_backtrace                         false
% 1.86/0.99  --dbg_dump_prop_clauses                 false
% 1.86/0.99  --dbg_dump_prop_clauses_file            -
% 1.86/0.99  --dbg_out_stat                          false
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  ------ Proving...
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  % SZS status Theorem for theBenchmark.p
% 1.86/0.99  
% 1.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.86/0.99  
% 1.86/0.99  fof(f10,conjecture,(
% 1.86/0.99    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0)))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f11,negated_conjecture,(
% 1.86/0.99    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0)))),
% 1.86/0.99    inference(negated_conjecture,[],[f10])).
% 1.86/0.99  
% 1.86/0.99  fof(f32,plain,(
% 1.86/0.99    ? [X0] : (? [X1] : (k3_lattices(X0,k6_lattices(X0),X1) != k6_lattices(X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f11])).
% 1.86/0.99  
% 1.86/0.99  fof(f33,plain,(
% 1.86/0.99    ? [X0] : (? [X1] : (k3_lattices(X0,k6_lattices(X0),X1) != k6_lattices(X0) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f32])).
% 1.86/0.99  
% 1.86/0.99  fof(f41,plain,(
% 1.86/0.99    ( ! [X0] : (? [X1] : (k3_lattices(X0,k6_lattices(X0),X1) != k6_lattices(X0) & m1_subset_1(X1,u1_struct_0(X0))) => (k3_lattices(X0,k6_lattices(X0),sK3) != k6_lattices(X0) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f40,plain,(
% 1.86/0.99    ? [X0] : (? [X1] : (k3_lattices(X0,k6_lattices(X0),X1) != k6_lattices(X0) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k3_lattices(sK2,k6_lattices(sK2),X1) != k6_lattices(sK2) & m1_subset_1(X1,u1_struct_0(sK2))) & l3_lattices(sK2) & v14_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2))),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f42,plain,(
% 1.86/0.99    (k3_lattices(sK2,k6_lattices(sK2),sK3) != k6_lattices(sK2) & m1_subset_1(sK3,u1_struct_0(sK2))) & l3_lattices(sK2) & v14_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2)),
% 1.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f41,f40])).
% 1.86/0.99  
% 1.86/0.99  fof(f64,plain,(
% 1.86/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.86/0.99    inference(cnf_transformation,[],[f42])).
% 1.86/0.99  
% 1.86/0.99  fof(f9,axiom,(
% 1.86/0.99    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f30,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f9])).
% 1.86/0.99  
% 1.86/0.99  fof(f31,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f30])).
% 1.86/0.99  
% 1.86/0.99  fof(f59,plain,(
% 1.86/0.99    ( ! [X0,X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f31])).
% 1.86/0.99  
% 1.86/0.99  fof(f62,plain,(
% 1.86/0.99    v14_lattices(sK2)),
% 1.86/0.99    inference(cnf_transformation,[],[f42])).
% 1.86/0.99  
% 1.86/0.99  fof(f60,plain,(
% 1.86/0.99    ~v2_struct_0(sK2)),
% 1.86/0.99    inference(cnf_transformation,[],[f42])).
% 1.86/0.99  
% 1.86/0.99  fof(f61,plain,(
% 1.86/0.99    v10_lattices(sK2)),
% 1.86/0.99    inference(cnf_transformation,[],[f42])).
% 1.86/0.99  
% 1.86/0.99  fof(f63,plain,(
% 1.86/0.99    l3_lattices(sK2)),
% 1.86/0.99    inference(cnf_transformation,[],[f42])).
% 1.86/0.99  
% 1.86/0.99  fof(f1,axiom,(
% 1.86/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f13,plain,(
% 1.86/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.86/0.99    inference(pure_predicate_removal,[],[f1])).
% 1.86/0.99  
% 1.86/0.99  fof(f14,plain,(
% 1.86/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.86/0.99    inference(pure_predicate_removal,[],[f13])).
% 1.86/0.99  
% 1.86/0.99  fof(f15,plain,(
% 1.86/0.99    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.86/0.99    inference(ennf_transformation,[],[f14])).
% 1.86/0.99  
% 1.86/0.99  fof(f16,plain,(
% 1.86/0.99    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.86/0.99    inference(flattening,[],[f15])).
% 1.86/0.99  
% 1.86/0.99  fof(f45,plain,(
% 1.86/0.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f16])).
% 1.86/0.99  
% 1.86/0.99  fof(f8,axiom,(
% 1.86/0.99    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f28,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f8])).
% 1.86/0.99  
% 1.86/0.99  fof(f29,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f28])).
% 1.86/0.99  
% 1.86/0.99  fof(f58,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f29])).
% 1.86/0.99  
% 1.86/0.99  fof(f46,plain,(
% 1.86/0.99    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f16])).
% 1.86/0.99  
% 1.86/0.99  fof(f7,axiom,(
% 1.86/0.99    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f26,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f7])).
% 1.86/0.99  
% 1.86/0.99  fof(f27,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f26])).
% 1.86/0.99  
% 1.86/0.99  fof(f39,plain,(
% 1.86/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(nnf_transformation,[],[f27])).
% 1.86/0.99  
% 1.86/0.99  fof(f56,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f39])).
% 1.86/0.99  
% 1.86/0.99  fof(f47,plain,(
% 1.86/0.99    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f16])).
% 1.86/0.99  
% 1.86/0.99  fof(f5,axiom,(
% 1.86/0.99    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f12,plain,(
% 1.86/0.99    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 1.86/0.99    inference(pure_predicate_removal,[],[f5])).
% 1.86/0.99  
% 1.86/0.99  fof(f23,plain,(
% 1.86/0.99    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 1.86/0.99    inference(ennf_transformation,[],[f12])).
% 1.86/0.99  
% 1.86/0.99  fof(f54,plain,(
% 1.86/0.99    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f23])).
% 1.86/0.99  
% 1.86/0.99  fof(f4,axiom,(
% 1.86/0.99    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f21,plain,(
% 1.86/0.99    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f4])).
% 1.86/0.99  
% 1.86/0.99  fof(f22,plain,(
% 1.86/0.99    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f21])).
% 1.86/0.99  
% 1.86/0.99  fof(f53,plain,(
% 1.86/0.99    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f22])).
% 1.86/0.99  
% 1.86/0.99  fof(f3,axiom,(
% 1.86/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f19,plain,(
% 1.86/0.99    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f3])).
% 1.86/0.99  
% 1.86/0.99  fof(f20,plain,(
% 1.86/0.99    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f19])).
% 1.86/0.99  
% 1.86/0.99  fof(f34,plain,(
% 1.86/0.99    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(nnf_transformation,[],[f20])).
% 1.86/0.99  
% 1.86/0.99  fof(f35,plain,(
% 1.86/0.99    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(rectify,[],[f34])).
% 1.86/0.99  
% 1.86/0.99  fof(f37,plain,(
% 1.86/0.99    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f36,plain,(
% 1.86/0.99    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f38,plain,(
% 1.86/0.99    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 1.86/0.99  
% 1.86/0.99  fof(f49,plain,(
% 1.86/0.99    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f38])).
% 1.86/0.99  
% 1.86/0.99  fof(f6,axiom,(
% 1.86/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f24,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f6])).
% 1.86/0.99  
% 1.86/0.99  fof(f25,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f24])).
% 1.86/0.99  
% 1.86/0.99  fof(f55,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f25])).
% 1.86/0.99  
% 1.86/0.99  fof(f44,plain,(
% 1.86/0.99    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f16])).
% 1.86/0.99  
% 1.86/0.99  fof(f2,axiom,(
% 1.86/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f17,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.86/0.99    inference(ennf_transformation,[],[f2])).
% 1.86/0.99  
% 1.86/0.99  fof(f18,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.86/0.99    inference(flattening,[],[f17])).
% 1.86/0.99  
% 1.86/0.99  fof(f48,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f18])).
% 1.86/0.99  
% 1.86/0.99  fof(f65,plain,(
% 1.86/0.99    k3_lattices(sK2,k6_lattices(sK2),sK3) != k6_lattices(sK2)),
% 1.86/0.99    inference(cnf_transformation,[],[f42])).
% 1.86/0.99  
% 1.86/0.99  cnf(c_18,negated_conjecture,
% 1.86/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.86/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_616,negated_conjecture,
% 1.86/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.86/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_756,plain,
% 1.86/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_16,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.86/0.99      | ~ v14_lattices(X1)
% 1.86/0.99      | ~ l3_lattices(X1)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v10_lattices(X1)
% 1.86/0.99      | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
% 1.86/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_20,negated_conjecture,
% 1.86/0.99      ( v14_lattices(sK2) ),
% 1.86/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_242,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.86/0.99      | ~ l3_lattices(X1)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | ~ v10_lattices(X1)
% 1.86/0.99      | k4_lattices(X1,k6_lattices(X1),X0) = X0
% 1.86/0.99      | sK2 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_243,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ l3_lattices(sK2)
% 1.86/0.99      | v2_struct_0(sK2)
% 1.86/0.99      | ~ v10_lattices(sK2)
% 1.86/0.99      | k4_lattices(sK2,k6_lattices(sK2),X0) = X0 ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_242]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_22,negated_conjecture,
% 1.86/0.99      ( ~ v2_struct_0(sK2) ),
% 1.86/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_21,negated_conjecture,
% 1.86/0.99      ( v10_lattices(sK2) ),
% 1.86/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_19,negated_conjecture,
% 1.86/0.99      ( l3_lattices(sK2) ),
% 1.86/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_247,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | k4_lattices(sK2,k6_lattices(sK2),X0) = X0 ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_243,c_22,c_21,c_19]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_615,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 1.86/0.99      | k4_lattices(sK2,k6_lattices(sK2),X0_49) = X0_49 ),
% 1.86/0.99      inference(subtyping,[status(esa)],[c_247]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_757,plain,
% 1.86/0.99      ( k4_lattices(sK2,k6_lattices(sK2),X0_49) = X0_49
% 1.86/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_846,plain,
% 1.86/0.99      ( k4_lattices(sK2,k6_lattices(sK2),sK3) = sK3 ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_756,c_757]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2,plain,
% 1.86/0.99      ( v6_lattices(X0)
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | ~ v10_lattices(X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_15,plain,
% 1.86/0.99      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.86/0.99      | ~ v6_lattices(X0)
% 1.86/0.99      | ~ v8_lattices(X0)
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_263,plain,
% 1.86/0.99      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.86/0.99      | ~ v8_lattices(X0)
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | ~ v10_lattices(X0) ),
% 1.86/0.99      inference(resolution,[status(thm)],[c_2,c_15]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1,plain,
% 1.86/0.99      ( v8_lattices(X0)
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | ~ v10_lattices(X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_267,plain,
% 1.86/0.99      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.86/0.99      | r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | ~ v10_lattices(X0) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_263,c_1]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_268,plain,
% 1.86/0.99      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | ~ v10_lattices(X0) ),
% 1.86/0.99      inference(renaming,[status(thm)],[c_267]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_299,plain,
% 1.86/0.99      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | sK2 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_268,c_21]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_300,plain,
% 1.86/0.99      ( r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0)
% 1.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | ~ l3_lattices(sK2)
% 1.86/0.99      | v2_struct_0(sK2) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_299]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_304,plain,
% 1.86/0.99      ( r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0)
% 1.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_300,c_22,c_19]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_14,plain,
% 1.86/0.99      ( ~ r1_lattices(X0,X1,X2)
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.86/0.99      | ~ v8_lattices(X0)
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | ~ v9_lattices(X0)
% 1.86/0.99      | k2_lattices(X0,X1,X2) = X1 ),
% 1.86/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_0,plain,
% 1.86/0.99      ( ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | ~ v10_lattices(X0)
% 1.86/0.99      | v9_lattices(X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_342,plain,
% 1.86/0.99      ( ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | v9_lattices(X0)
% 1.86/0.99      | sK2 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_343,plain,
% 1.86/0.99      ( ~ l3_lattices(sK2) | v2_struct_0(sK2) | v9_lattices(sK2) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_342]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_75,plain,
% 1.86/0.99      ( ~ l3_lattices(sK2)
% 1.86/0.99      | v2_struct_0(sK2)
% 1.86/0.99      | ~ v10_lattices(sK2)
% 1.86/0.99      | v9_lattices(sK2) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_345,plain,
% 1.86/0.99      ( v9_lattices(sK2) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_343,c_22,c_21,c_19,c_75]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_431,plain,
% 1.86/0.99      ( ~ r1_lattices(X0,X1,X2)
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.86/0.99      | ~ v8_lattices(X0)
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | k2_lattices(X0,X1,X2) = X1
% 1.86/0.99      | sK2 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_345]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_432,plain,
% 1.86/0.99      ( ~ r1_lattices(sK2,X0,X1)
% 1.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | ~ v8_lattices(sK2)
% 1.86/0.99      | ~ l3_lattices(sK2)
% 1.86/0.99      | v2_struct_0(sK2)
% 1.86/0.99      | k2_lattices(sK2,X0,X1) = X0 ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_431]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_72,plain,
% 1.86/0.99      ( v8_lattices(sK2)
% 1.86/0.99      | ~ l3_lattices(sK2)
% 1.86/0.99      | v2_struct_0(sK2)
% 1.86/0.99      | ~ v10_lattices(sK2) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_436,plain,
% 1.86/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ r1_lattices(sK2,X0,X1)
% 1.86/0.99      | k2_lattices(sK2,X0,X1) = X0 ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_432,c_22,c_21,c_19,c_72]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_437,plain,
% 1.86/0.99      ( ~ r1_lattices(sK2,X0,X1)
% 1.86/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | k2_lattices(sK2,X0,X1) = X0 ),
% 1.86/0.99      inference(renaming,[status(thm)],[c_436]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_490,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.86/0.99      | X3 != X0
% 1.86/0.99      | k4_lattices(sK2,X0,X1) != X2
% 1.86/0.99      | k2_lattices(sK2,X2,X3) = X2
% 1.86/0.99      | sK2 != sK2 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_304,c_437]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_491,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(k4_lattices(sK2,X0,X1),u1_struct_0(sK2))
% 1.86/0.99      | k2_lattices(sK2,k4_lattices(sK2,X0,X1),X0) = k4_lattices(sK2,X0,X1) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_612,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(k4_lattices(sK2,X0_49,X1_49),u1_struct_0(sK2))
% 1.86/0.99      | k2_lattices(sK2,k4_lattices(sK2,X0_49,X1_49),X0_49) = k4_lattices(sK2,X0_49,X1_49) ),
% 1.86/0.99      inference(subtyping,[status(esa)],[c_491]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_760,plain,
% 1.86/0.99      ( k2_lattices(sK2,k4_lattices(sK2,X0_49,X1_49),X0_49) = k4_lattices(sK2,X0_49,X1_49)
% 1.86/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 1.86/0.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
% 1.86/0.99      | m1_subset_1(k4_lattices(sK2,X0_49,X1_49),u1_struct_0(sK2)) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1689,plain,
% 1.86/0.99      ( k2_lattices(sK2,k4_lattices(sK2,k6_lattices(sK2),sK3),k6_lattices(sK2)) = k4_lattices(sK2,k6_lattices(sK2),sK3)
% 1.86/0.99      | m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) != iProver_top
% 1.86/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_846,c_760]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1699,plain,
% 1.86/0.99      ( k2_lattices(sK2,sK3,k6_lattices(sK2)) = sK3
% 1.86/0.99      | m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) != iProver_top
% 1.86/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.86/0.99      inference(light_normalisation,[status(thm)],[c_1689,c_846]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_23,plain,
% 1.86/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_26,plain,
% 1.86/0.99      ( l3_lattices(sK2) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_27,plain,
% 1.86/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_11,plain,
% 1.86/0.99      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_43,plain,
% 1.86/0.99      ( l2_lattices(X0) = iProver_top | l3_lattices(X0) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_45,plain,
% 1.86/0.99      ( l2_lattices(sK2) = iProver_top
% 1.86/0.99      | l3_lattices(sK2) != iProver_top ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_43]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_10,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 1.86/0.99      | ~ l2_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_46,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) = iProver_top
% 1.86/0.99      | l2_lattices(X0) != iProver_top
% 1.86/0.99      | v2_struct_0(X0) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_48,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) = iProver_top
% 1.86/0.99      | l2_lattices(sK2) != iProver_top
% 1.86/0.99      | v2_struct_0(sK2) = iProver_top ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_46]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1969,plain,
% 1.86/0.99      ( k2_lattices(sK2,sK3,k6_lattices(sK2)) = sK3 ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_1699,c_23,c_26,c_27,c_45,c_48]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_413,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0) ),
% 1.86/0.99      inference(resolution,[status(thm)],[c_11,c_10]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_513,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | sK2 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_413,c_22]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_514,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2))
% 1.86/0.99      | ~ l3_lattices(sK2) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_513]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_44,plain,
% 1.86/0.99      ( l2_lattices(sK2) | ~ l3_lattices(sK2) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_47,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2))
% 1.86/0.99      | ~ l2_lattices(sK2)
% 1.86/0.99      | v2_struct_0(sK2) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_516,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_514,c_22,c_19,c_44,c_47]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_611,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) ),
% 1.86/0.99      inference(subtyping,[status(esa)],[c_516]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_761,plain,
% 1.86/0.99      ( m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2)) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_9,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.86/0.99      | ~ v8_lattices(X1)
% 1.86/0.99      | ~ l3_lattices(X1)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 1.86/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_530,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.86/0.99      | ~ v8_lattices(X1)
% 1.86/0.99      | ~ l3_lattices(X1)
% 1.86/0.99      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 1.86/0.99      | sK2 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_531,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | ~ v8_lattices(sK2)
% 1.86/0.99      | ~ l3_lattices(sK2)
% 1.86/0.99      | k1_lattices(sK2,k2_lattices(sK2,X1,X0),X0) = X0 ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_530]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_535,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | k1_lattices(sK2,k2_lattices(sK2,X1,X0),X0) = X0 ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_531,c_22,c_21,c_19,c_72]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_610,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 1.86/0.99      | k1_lattices(sK2,k2_lattices(sK2,X1_49,X0_49),X0_49) = X0_49 ),
% 1.86/0.99      inference(subtyping,[status(esa)],[c_535]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_762,plain,
% 1.86/0.99      ( k1_lattices(sK2,k2_lattices(sK2,X0_49,X1_49),X1_49) = X1_49
% 1.86/0.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
% 1.86/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_905,plain,
% 1.86/0.99      ( k1_lattices(sK2,k2_lattices(sK2,sK3,X0_49),X0_49) = X0_49
% 1.86/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_756,c_762]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_963,plain,
% 1.86/0.99      ( k1_lattices(sK2,k2_lattices(sK2,sK3,k6_lattices(sK2)),k6_lattices(sK2)) = k6_lattices(sK2) ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_761,c_905]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1972,plain,
% 1.86/0.99      ( k1_lattices(sK2,sK3,k6_lattices(sK2)) = k6_lattices(sK2) ),
% 1.86/0.99      inference(demodulation,[status(thm)],[c_1969,c_963]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_12,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.86/0.99      | ~ l2_lattices(X1)
% 1.86/0.99      | ~ v4_lattices(X1)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_3,plain,
% 1.86/0.99      ( v4_lattices(X0)
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | ~ v10_lattices(X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_320,plain,
% 1.86/0.99      ( v4_lattices(X0)
% 1.86/0.99      | ~ l3_lattices(X0)
% 1.86/0.99      | v2_struct_0(X0)
% 1.86/0.99      | sK2 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_321,plain,
% 1.86/0.99      ( v4_lattices(sK2) | ~ l3_lattices(sK2) | v2_struct_0(sK2) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_66,plain,
% 1.86/0.99      ( v4_lattices(sK2)
% 1.86/0.99      | ~ l3_lattices(sK2)
% 1.86/0.99      | v2_struct_0(sK2)
% 1.86/0.99      | ~ v10_lattices(sK2) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_323,plain,
% 1.86/0.99      ( v4_lattices(sK2) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_321,c_22,c_21,c_19,c_66]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_363,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.86/0.99      | ~ l2_lattices(X1)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 1.86/0.99      | sK2 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_323]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_364,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | ~ l2_lattices(sK2)
% 1.86/0.99      | v2_struct_0(sK2)
% 1.86/0.99      | k1_lattices(sK2,X1,X0) = k3_lattices(sK2,X1,X0) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_363]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_368,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | k1_lattices(sK2,X1,X0) = k3_lattices(sK2,X1,X0) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_364,c_22,c_19,c_44]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_614,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 1.86/0.99      | k1_lattices(sK2,X1_49,X0_49) = k3_lattices(sK2,X1_49,X0_49) ),
% 1.86/0.99      inference(subtyping,[status(esa)],[c_368]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_758,plain,
% 1.86/0.99      ( k1_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X0_49,X1_49)
% 1.86/0.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
% 1.86/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1007,plain,
% 1.86/0.99      ( k1_lattices(sK2,sK3,X0_49) = k3_lattices(sK2,sK3,X0_49)
% 1.86/0.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_756,c_758]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1025,plain,
% 1.86/0.99      ( k1_lattices(sK2,sK3,k6_lattices(sK2)) = k3_lattices(sK2,sK3,k6_lattices(sK2)) ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_761,c_1007]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2084,plain,
% 1.86/0.99      ( k3_lattices(sK2,sK3,k6_lattices(sK2)) = k6_lattices(sK2) ),
% 1.86/0.99      inference(demodulation,[status(thm)],[c_1972,c_1025]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_620,plain,
% 1.86/0.99      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 1.86/0.99      theory(equality) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_926,plain,
% 1.86/0.99      ( X0_49 != X1_49
% 1.86/0.99      | k4_lattices(sK2,X2_49,X3_49) != X1_49
% 1.86/0.99      | k4_lattices(sK2,X2_49,X3_49) = X0_49 ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_620]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_989,plain,
% 1.86/0.99      ( X0_49 != X1_49
% 1.86/0.99      | k4_lattices(sK2,k6_lattices(sK2),X1_49) != X1_49
% 1.86/0.99      | k4_lattices(sK2,k6_lattices(sK2),X1_49) = X0_49 ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_926]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1444,plain,
% 1.86/0.99      ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) = k3_lattices(sK2,sK3,k6_lattices(sK2))
% 1.86/0.99      | k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) != k6_lattices(sK2)
% 1.86/0.99      | k3_lattices(sK2,sK3,k6_lattices(sK2)) != k6_lattices(sK2) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_989]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_5,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.86/0.99      | ~ l2_lattices(X1)
% 1.86/0.99      | ~ v4_lattices(X1)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_384,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.86/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.86/0.99      | ~ l2_lattices(X1)
% 1.86/0.99      | v2_struct_0(X1)
% 1.86/0.99      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 1.86/0.99      | sK2 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_323]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_385,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | ~ l2_lattices(sK2)
% 1.86/0.99      | v2_struct_0(sK2)
% 1.86/0.99      | k3_lattices(sK2,X1,X0) = k3_lattices(sK2,X0,X1) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_384]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_389,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.86/0.99      | k3_lattices(sK2,X1,X0) = k3_lattices(sK2,X0,X1) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_385,c_22,c_19,c_44]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_613,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 1.86/0.99      | k3_lattices(sK2,X1_49,X0_49) = k3_lattices(sK2,X0_49,X1_49) ),
% 1.86/0.99      inference(subtyping,[status(esa)],[c_389]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1074,plain,
% 1.86/0.99      ( ~ m1_subset_1(k6_lattices(sK2),u1_struct_0(sK2))
% 1.86/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.86/0.99      | k3_lattices(sK2,k6_lattices(sK2),sK3) = k3_lattices(sK2,sK3,k6_lattices(sK2)) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_613]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1001,plain,
% 1.86/0.99      ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) != X0_49
% 1.86/0.99      | k3_lattices(sK2,k6_lattices(sK2),sK3) != X0_49
% 1.86/0.99      | k3_lattices(sK2,k6_lattices(sK2),sK3) = k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_620]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1073,plain,
% 1.86/0.99      ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) != k3_lattices(sK2,sK3,k6_lattices(sK2))
% 1.86/0.99      | k3_lattices(sK2,k6_lattices(sK2),sK3) = k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2))
% 1.86/0.99      | k3_lattices(sK2,k6_lattices(sK2),sK3) != k3_lattices(sK2,sK3,k6_lattices(sK2)) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_1001]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_814,plain,
% 1.86/0.99      ( k3_lattices(sK2,k6_lattices(sK2),sK3) != X0_49
% 1.86/0.99      | k3_lattices(sK2,k6_lattices(sK2),sK3) = k6_lattices(sK2)
% 1.86/0.99      | k6_lattices(sK2) != X0_49 ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_620]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_969,plain,
% 1.86/0.99      ( k3_lattices(sK2,k6_lattices(sK2),sK3) != k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2))
% 1.86/0.99      | k3_lattices(sK2,k6_lattices(sK2),sK3) = k6_lattices(sK2)
% 1.86/0.99      | k6_lattices(sK2) != k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_814]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_826,plain,
% 1.86/0.99      ( X0_49 != X1_49
% 1.86/0.99      | k6_lattices(sK2) != X1_49
% 1.86/0.99      | k6_lattices(sK2) = X0_49 ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_620]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_852,plain,
% 1.86/0.99      ( X0_49 != k6_lattices(sK2)
% 1.86/0.99      | k6_lattices(sK2) = X0_49
% 1.86/0.99      | k6_lattices(sK2) != k6_lattices(sK2) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_826]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_919,plain,
% 1.86/0.99      ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) != k6_lattices(sK2)
% 1.86/0.99      | k6_lattices(sK2) = k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2))
% 1.86/0.99      | k6_lattices(sK2) != k6_lattices(sK2) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_852]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_619,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_853,plain,
% 1.86/0.99      ( k6_lattices(sK2) = k6_lattices(sK2) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_619]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_847,plain,
% 1.86/0.99      ( k4_lattices(sK2,k6_lattices(sK2),k6_lattices(sK2)) = k6_lattices(sK2) ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_761,c_757]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_17,negated_conjecture,
% 1.86/0.99      ( k3_lattices(sK2,k6_lattices(sK2),sK3) != k6_lattices(sK2) ),
% 1.86/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_617,negated_conjecture,
% 1.86/0.99      ( k3_lattices(sK2,k6_lattices(sK2),sK3) != k6_lattices(sK2) ),
% 1.86/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(contradiction,plain,
% 1.86/0.99      ( $false ),
% 1.86/0.99      inference(minisat,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_2084,c_1444,c_1074,c_1073,c_969,c_919,c_853,c_847,
% 1.86/0.99                 c_617,c_47,c_44,c_18,c_19,c_22]) ).
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.86/0.99  
% 1.86/0.99  ------                               Statistics
% 1.86/0.99  
% 1.86/0.99  ------ General
% 1.86/0.99  
% 1.86/0.99  abstr_ref_over_cycles:                  0
% 1.86/0.99  abstr_ref_under_cycles:                 0
% 1.86/0.99  gc_basic_clause_elim:                   0
% 1.86/0.99  forced_gc_time:                         0
% 1.86/0.99  parsing_time:                           0.009
% 1.86/0.99  unif_index_cands_time:                  0.
% 1.86/0.99  unif_index_add_time:                    0.
% 1.86/0.99  orderings_time:                         0.
% 1.86/0.99  out_proof_time:                         0.013
% 1.86/0.99  total_time:                             0.115
% 1.86/0.99  num_of_symbols:                         52
% 1.86/0.99  num_of_terms:                           1690
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing
% 1.86/0.99  
% 1.86/0.99  num_of_splits:                          0
% 1.86/0.99  num_of_split_atoms:                     0
% 1.86/0.99  num_of_reused_defs:                     0
% 1.86/0.99  num_eq_ax_congr_red:                    26
% 1.86/0.99  num_of_sem_filtered_clauses:            1
% 1.86/0.99  num_of_subtypes:                        3
% 1.86/0.99  monotx_restored_types:                  0
% 1.86/0.99  sat_num_of_epr_types:                   0
% 1.86/0.99  sat_num_of_non_cyclic_types:            0
% 1.86/0.99  sat_guarded_non_collapsed_types:        1
% 1.86/0.99  num_pure_diseq_elim:                    0
% 1.86/0.99  simp_replaced_by:                       0
% 1.86/0.99  res_preprocessed:                       61
% 1.86/0.99  prep_upred:                             0
% 1.86/0.99  prep_unflattend:                        16
% 1.86/0.99  smt_new_axioms:                         0
% 1.86/0.99  pred_elim_cands:                        1
% 1.86/0.99  pred_elim:                              10
% 1.86/0.99  pred_elim_cl:                           14
% 1.86/0.99  pred_elim_cycles:                       12
% 1.86/0.99  merged_defs:                            0
% 1.86/0.99  merged_defs_ncl:                        0
% 1.86/0.99  bin_hyper_res:                          0
% 1.86/0.99  prep_cycles:                            4
% 1.86/0.99  pred_elim_time:                         0.006
% 1.86/0.99  splitting_time:                         0.
% 1.86/0.99  sem_filter_time:                        0.
% 1.86/0.99  monotx_time:                            0.
% 1.86/0.99  subtype_inf_time:                       0.
% 1.86/0.99  
% 1.86/0.99  ------ Problem properties
% 1.86/0.99  
% 1.86/0.99  clauses:                                8
% 1.86/0.99  conjectures:                            2
% 1.86/0.99  epr:                                    0
% 1.86/0.99  horn:                                   8
% 1.86/0.99  ground:                                 3
% 1.86/0.99  unary:                                  3
% 1.86/0.99  binary:                                 1
% 1.86/0.99  lits:                                   18
% 1.86/0.99  lits_eq:                                6
% 1.86/0.99  fd_pure:                                0
% 1.86/0.99  fd_pseudo:                              0
% 1.86/0.99  fd_cond:                                0
% 1.86/0.99  fd_pseudo_cond:                         0
% 1.86/0.99  ac_symbols:                             0
% 1.86/0.99  
% 1.86/0.99  ------ Propositional Solver
% 1.86/0.99  
% 1.86/0.99  prop_solver_calls:                      29
% 1.86/0.99  prop_fast_solver_calls:                 490
% 1.86/0.99  smt_solver_calls:                       0
% 1.86/0.99  smt_fast_solver_calls:                  0
% 1.86/0.99  prop_num_of_clauses:                    647
% 1.86/0.99  prop_preprocess_simplified:             2169
% 1.86/0.99  prop_fo_subsumed:                       27
% 1.86/0.99  prop_solver_time:                       0.
% 1.86/0.99  smt_solver_time:                        0.
% 1.86/0.99  smt_fast_solver_time:                   0.
% 1.86/0.99  prop_fast_solver_time:                  0.
% 1.86/0.99  prop_unsat_core_time:                   0.
% 1.86/0.99  
% 1.86/0.99  ------ QBF
% 1.86/0.99  
% 1.86/0.99  qbf_q_res:                              0
% 1.86/0.99  qbf_num_tautologies:                    0
% 1.86/0.99  qbf_prep_cycles:                        0
% 1.86/0.99  
% 1.86/0.99  ------ BMC1
% 1.86/0.99  
% 1.86/0.99  bmc1_current_bound:                     -1
% 1.86/0.99  bmc1_last_solved_bound:                 -1
% 1.86/0.99  bmc1_unsat_core_size:                   -1
% 1.86/0.99  bmc1_unsat_core_parents_size:           -1
% 1.86/0.99  bmc1_merge_next_fun:                    0
% 1.86/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.86/0.99  
% 1.86/0.99  ------ Instantiation
% 1.86/0.99  
% 1.86/0.99  inst_num_of_clauses:                    258
% 1.86/0.99  inst_num_in_passive:                    117
% 1.86/0.99  inst_num_in_active:                     141
% 1.86/0.99  inst_num_in_unprocessed:                0
% 1.86/0.99  inst_num_of_loops:                      150
% 1.86/0.99  inst_num_of_learning_restarts:          0
% 1.86/0.99  inst_num_moves_active_passive:          2
% 1.86/0.99  inst_lit_activity:                      0
% 1.86/0.99  inst_lit_activity_moves:                0
% 1.86/0.99  inst_num_tautologies:                   0
% 1.86/0.99  inst_num_prop_implied:                  0
% 1.86/0.99  inst_num_existing_simplified:           0
% 1.86/0.99  inst_num_eq_res_simplified:             0
% 1.86/0.99  inst_num_child_elim:                    0
% 1.86/0.99  inst_num_of_dismatching_blockings:      125
% 1.86/0.99  inst_num_of_non_proper_insts:           376
% 1.86/0.99  inst_num_of_duplicates:                 0
% 1.86/0.99  inst_inst_num_from_inst_to_res:         0
% 1.86/0.99  inst_dismatching_checking_time:         0.
% 1.86/0.99  
% 1.86/0.99  ------ Resolution
% 1.86/0.99  
% 1.86/0.99  res_num_of_clauses:                     0
% 1.86/0.99  res_num_in_passive:                     0
% 1.86/0.99  res_num_in_active:                      0
% 1.86/0.99  res_num_of_loops:                       65
% 1.86/0.99  res_forward_subset_subsumed:            39
% 1.86/0.99  res_backward_subset_subsumed:           0
% 1.86/0.99  res_forward_subsumed:                   0
% 1.86/0.99  res_backward_subsumed:                  0
% 1.86/0.99  res_forward_subsumption_resolution:     0
% 1.86/0.99  res_backward_subsumption_resolution:    0
% 1.86/0.99  res_clause_to_clause_subsumption:       39
% 1.86/0.99  res_orphan_elimination:                 0
% 1.86/0.99  res_tautology_del:                      85
% 1.86/0.99  res_num_eq_res_simplified:              0
% 1.86/0.99  res_num_sel_changes:                    0
% 1.86/0.99  res_moves_from_active_to_pass:          0
% 1.86/0.99  
% 1.86/0.99  ------ Superposition
% 1.86/0.99  
% 1.86/0.99  sup_time_total:                         0.
% 1.86/0.99  sup_time_generating:                    0.
% 1.86/0.99  sup_time_sim_full:                      0.
% 1.86/0.99  sup_time_sim_immed:                     0.
% 1.86/0.99  
% 1.86/0.99  sup_num_of_clauses:                     27
% 1.86/0.99  sup_num_in_active:                      24
% 1.86/0.99  sup_num_in_passive:                     3
% 1.86/0.99  sup_num_of_loops:                       28
% 1.86/0.99  sup_fw_superposition:                   22
% 1.86/0.99  sup_bw_superposition:                   0
% 1.86/0.99  sup_immediate_simplified:               2
% 1.86/0.99  sup_given_eliminated:                   0
% 1.86/0.99  comparisons_done:                       0
% 1.86/0.99  comparisons_avoided:                    0
% 1.86/0.99  
% 1.86/0.99  ------ Simplifications
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  sim_fw_subset_subsumed:                 0
% 1.86/0.99  sim_bw_subset_subsumed:                 0
% 1.86/0.99  sim_fw_subsumed:                        0
% 1.86/0.99  sim_bw_subsumed:                        0
% 1.86/0.99  sim_fw_subsumption_res:                 0
% 1.86/0.99  sim_bw_subsumption_res:                 0
% 1.86/0.99  sim_tautology_del:                      0
% 1.86/0.99  sim_eq_tautology_del:                   2
% 1.86/0.99  sim_eq_res_simp:                        0
% 1.86/0.99  sim_fw_demodulated:                     0
% 1.86/0.99  sim_bw_demodulated:                     4
% 1.86/0.99  sim_light_normalised:                   2
% 1.86/0.99  sim_joinable_taut:                      0
% 1.86/0.99  sim_joinable_simp:                      0
% 1.86/0.99  sim_ac_normalised:                      0
% 1.86/0.99  sim_smt_subsumption:                    0
% 1.86/0.99  
%------------------------------------------------------------------------------
