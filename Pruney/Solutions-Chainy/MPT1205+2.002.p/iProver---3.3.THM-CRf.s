%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:16 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 301 expanded)
%              Number of clauses        :   58 (  78 expanded)
%              Number of leaves         :   13 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  525 (1580 expanded)
%              Number of equality atoms :  119 ( 284 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k3_lattices(X0,k5_lattices(X0),sK2) != sK2
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_lattices(X0,k5_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k3_lattices(sK1,k5_lattices(sK1),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v13_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k3_lattices(sK1,k5_lattices(sK1),sK2) != sK2
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v13_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f35,f34])).

fof(f54,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f36])).

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
          & v8_lattices(X0)
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
          & v8_lattices(X0)
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
          & v8_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f40,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
    v13_lattices(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    k3_lattices(sK1,k5_lattices(sK1),sK2) != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_734,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1038,plain,
    ( k1_lattices(sK1,k5_lattices(sK1),sK2) != X0_47
    | sK2 != X0_47
    | sK2 = k1_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_1039,plain,
    ( k1_lattices(sK1,k5_lattices(sK1),sK2) != sK2
    | sK2 = k1_lattices(sK1,k5_lattices(sK1),sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_20,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_11,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_230,c_11])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_248])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | k3_lattices(sK1,X1,X0) = k1_lattices(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k3_lattices(sK1,X1,X0) = k1_lattices(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_21,c_18])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK1))
    | k3_lattices(sK1,X1_47,X0_47) = k1_lattices(sK1,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_292])).

cnf(c_1009,plain,
    ( ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k3_lattices(sK1,k5_lattices(sK1),sK2) = k1_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_994,plain,
    ( k3_lattices(sK1,k5_lattices(sK1),sK2) != X0_47
    | k3_lattices(sK1,k5_lattices(sK1),sK2) = sK2
    | sK2 != X0_47 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_1008,plain,
    ( k3_lattices(sK1,k5_lattices(sK1),sK2) != k1_lattices(sK1,k5_lattices(sK1),sK2)
    | k3_lattices(sK1,k5_lattices(sK1),sK2) = sK2
    | sK2 != k1_lattices(sK1,k5_lattices(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_14,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_276,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_277,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | v9_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_71,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | v9_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_279,plain,
    ( v9_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_21,c_20,c_18,c_71])).

cnf(c_400,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_279])).

cnf(c_401,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | k2_lattices(sK1,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_68,plain,
    ( v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r1_lattices(sK1,X0,X1)
    | k2_lattices(sK1,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_21,c_20,c_18,c_68])).

cnf(c_406,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k2_lattices(sK1,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_405])).

cnf(c_9,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_316,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(resolution,[status(thm)],[c_11,c_9])).

cnf(c_458,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_316,c_18])).

cnf(c_459,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | k1_lattices(sK1,X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r1_lattices(sK1,X0,X1)
    | k1_lattices(sK1,X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_21])).

cnf(c_464,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k1_lattices(sK1,X0,X1) = X1 ),
    inference(renaming,[status(thm)],[c_463])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k1_lattices(sK1,X0,X1) = X1
    | k2_lattices(sK1,X0,X1) != X0 ),
    inference(resolution,[status(thm)],[c_406,c_464])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK1))
    | k1_lattices(sK1,X0_47,X1_47) = X1_47
    | k2_lattices(sK1,X0_47,X1_47) != X0_47 ),
    inference(subtyping,[status(esa)],[c_628])).

cnf(c_984,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | k1_lattices(sK1,k5_lattices(sK1),X0_47) = X0_47
    | k2_lattices(sK1,k5_lattices(sK1),X0_47) != k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_986,plain,
    ( ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k1_lattices(sK1,k5_lattices(sK1),sK2) = sK2
    | k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( v13_lattices(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1)
    | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_12,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_37,plain,
    ( l1_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_43,plain,
    ( m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_21,c_18,c_37,c_43])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),X0_47) = k5_lattices(sK1) ),
    inference(subtyping,[status(esa)],[c_506])).

cnf(c_748,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k2_lattices(sK1,k5_lattices(sK1),sK2) = k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_16,negated_conjecture,
    ( k3_lattices(sK1,k5_lattices(sK1),sK2) != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_731,negated_conjecture,
    ( k3_lattices(sK1,k5_lattices(sK1),sK2) != sK2 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_733,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_742,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1039,c_1009,c_1008,c_986,c_748,c_731,c_742,c_43,c_37,c_17,c_18,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n011.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 09:38:42 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running in FOF mode
% 1.01/0.91  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.01/0.91  
% 1.01/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.01/0.91  
% 1.01/0.91  ------  iProver source info
% 1.01/0.91  
% 1.01/0.91  git: date: 2020-06-30 10:37:57 +0100
% 1.01/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.01/0.91  git: non_committed_changes: false
% 1.01/0.91  git: last_make_outside_of_git: false
% 1.01/0.91  
% 1.01/0.91  ------ 
% 1.01/0.91  
% 1.01/0.91  ------ Input Options
% 1.01/0.91  
% 1.01/0.91  --out_options                           all
% 1.01/0.91  --tptp_safe_out                         true
% 1.01/0.91  --problem_path                          ""
% 1.01/0.91  --include_path                          ""
% 1.01/0.91  --clausifier                            res/vclausify_rel
% 1.01/0.91  --clausifier_options                    --mode clausify
% 1.01/0.91  --stdin                                 false
% 1.01/0.91  --stats_out                             all
% 1.01/0.91  
% 1.01/0.91  ------ General Options
% 1.01/0.91  
% 1.01/0.91  --fof                                   false
% 1.01/0.91  --time_out_real                         305.
% 1.01/0.91  --time_out_virtual                      -1.
% 1.01/0.91  --symbol_type_check                     false
% 1.01/0.91  --clausify_out                          false
% 1.01/0.91  --sig_cnt_out                           false
% 1.01/0.91  --trig_cnt_out                          false
% 1.01/0.91  --trig_cnt_out_tolerance                1.
% 1.01/0.91  --trig_cnt_out_sk_spl                   false
% 1.01/0.91  --abstr_cl_out                          false
% 1.01/0.91  
% 1.01/0.91  ------ Global Options
% 1.01/0.91  
% 1.01/0.91  --schedule                              default
% 1.01/0.91  --add_important_lit                     false
% 1.01/0.91  --prop_solver_per_cl                    1000
% 1.01/0.91  --min_unsat_core                        false
% 1.01/0.91  --soft_assumptions                      false
% 1.01/0.91  --soft_lemma_size                       3
% 1.01/0.91  --prop_impl_unit_size                   0
% 1.01/0.91  --prop_impl_unit                        []
% 1.01/0.91  --share_sel_clauses                     true
% 1.01/0.91  --reset_solvers                         false
% 1.01/0.91  --bc_imp_inh                            [conj_cone]
% 1.01/0.91  --conj_cone_tolerance                   3.
% 1.01/0.91  --extra_neg_conj                        none
% 1.01/0.91  --large_theory_mode                     true
% 1.01/0.91  --prolific_symb_bound                   200
% 1.01/0.91  --lt_threshold                          2000
% 1.01/0.91  --clause_weak_htbl                      true
% 1.01/0.91  --gc_record_bc_elim                     false
% 1.01/0.91  
% 1.01/0.91  ------ Preprocessing Options
% 1.01/0.91  
% 1.01/0.91  --preprocessing_flag                    true
% 1.01/0.91  --time_out_prep_mult                    0.1
% 1.01/0.91  --splitting_mode                        input
% 1.01/0.91  --splitting_grd                         true
% 1.01/0.91  --splitting_cvd                         false
% 1.01/0.91  --splitting_cvd_svl                     false
% 1.01/0.91  --splitting_nvd                         32
% 1.01/0.91  --sub_typing                            true
% 1.01/0.91  --prep_gs_sim                           true
% 1.01/0.91  --prep_unflatten                        true
% 1.01/0.91  --prep_res_sim                          true
% 1.01/0.91  --prep_upred                            true
% 1.01/0.91  --prep_sem_filter                       exhaustive
% 1.01/0.91  --prep_sem_filter_out                   false
% 1.01/0.91  --pred_elim                             true
% 1.01/0.91  --res_sim_input                         true
% 1.01/0.91  --eq_ax_congr_red                       true
% 1.01/0.91  --pure_diseq_elim                       true
% 1.01/0.91  --brand_transform                       false
% 1.01/0.91  --non_eq_to_eq                          false
% 1.01/0.91  --prep_def_merge                        true
% 1.01/0.91  --prep_def_merge_prop_impl              false
% 1.01/0.91  --prep_def_merge_mbd                    true
% 1.01/0.91  --prep_def_merge_tr_red                 false
% 1.01/0.91  --prep_def_merge_tr_cl                  false
% 1.01/0.91  --smt_preprocessing                     true
% 1.01/0.91  --smt_ac_axioms                         fast
% 1.01/0.91  --preprocessed_out                      false
% 1.01/0.91  --preprocessed_stats                    false
% 1.01/0.91  
% 1.01/0.91  ------ Abstraction refinement Options
% 1.01/0.91  
% 1.01/0.91  --abstr_ref                             []
% 1.01/0.91  --abstr_ref_prep                        false
% 1.01/0.91  --abstr_ref_until_sat                   false
% 1.01/0.91  --abstr_ref_sig_restrict                funpre
% 1.01/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/0.91  --abstr_ref_under                       []
% 1.01/0.91  
% 1.01/0.91  ------ SAT Options
% 1.01/0.91  
% 1.01/0.91  --sat_mode                              false
% 1.01/0.91  --sat_fm_restart_options                ""
% 1.01/0.91  --sat_gr_def                            false
% 1.01/0.91  --sat_epr_types                         true
% 1.01/0.91  --sat_non_cyclic_types                  false
% 1.01/0.91  --sat_finite_models                     false
% 1.01/0.91  --sat_fm_lemmas                         false
% 1.01/0.91  --sat_fm_prep                           false
% 1.01/0.91  --sat_fm_uc_incr                        true
% 1.01/0.91  --sat_out_model                         small
% 1.01/0.91  --sat_out_clauses                       false
% 1.01/0.91  
% 1.01/0.91  ------ QBF Options
% 1.01/0.91  
% 1.01/0.91  --qbf_mode                              false
% 1.01/0.91  --qbf_elim_univ                         false
% 1.01/0.91  --qbf_dom_inst                          none
% 1.01/0.91  --qbf_dom_pre_inst                      false
% 1.01/0.91  --qbf_sk_in                             false
% 1.01/0.91  --qbf_pred_elim                         true
% 1.01/0.91  --qbf_split                             512
% 1.01/0.91  
% 1.01/0.91  ------ BMC1 Options
% 1.01/0.91  
% 1.01/0.91  --bmc1_incremental                      false
% 1.01/0.91  --bmc1_axioms                           reachable_all
% 1.01/0.91  --bmc1_min_bound                        0
% 1.01/0.91  --bmc1_max_bound                        -1
% 1.01/0.91  --bmc1_max_bound_default                -1
% 1.01/0.91  --bmc1_symbol_reachability              true
% 1.01/0.91  --bmc1_property_lemmas                  false
% 1.01/0.91  --bmc1_k_induction                      false
% 1.01/0.91  --bmc1_non_equiv_states                 false
% 1.01/0.91  --bmc1_deadlock                         false
% 1.01/0.91  --bmc1_ucm                              false
% 1.01/0.91  --bmc1_add_unsat_core                   none
% 1.01/0.91  --bmc1_unsat_core_children              false
% 1.01/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/0.91  --bmc1_out_stat                         full
% 1.01/0.91  --bmc1_ground_init                      false
% 1.01/0.91  --bmc1_pre_inst_next_state              false
% 1.01/0.91  --bmc1_pre_inst_state                   false
% 1.01/0.91  --bmc1_pre_inst_reach_state             false
% 1.01/0.91  --bmc1_out_unsat_core                   false
% 1.01/0.91  --bmc1_aig_witness_out                  false
% 1.01/0.91  --bmc1_verbose                          false
% 1.01/0.91  --bmc1_dump_clauses_tptp                false
% 1.01/0.91  --bmc1_dump_unsat_core_tptp             false
% 1.01/0.91  --bmc1_dump_file                        -
% 1.01/0.91  --bmc1_ucm_expand_uc_limit              128
% 1.01/0.91  --bmc1_ucm_n_expand_iterations          6
% 1.01/0.91  --bmc1_ucm_extend_mode                  1
% 1.01/0.91  --bmc1_ucm_init_mode                    2
% 1.01/0.91  --bmc1_ucm_cone_mode                    none
% 1.01/0.91  --bmc1_ucm_reduced_relation_type        0
% 1.01/0.91  --bmc1_ucm_relax_model                  4
% 1.01/0.91  --bmc1_ucm_full_tr_after_sat            true
% 1.01/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/0.91  --bmc1_ucm_layered_model                none
% 1.01/0.91  --bmc1_ucm_max_lemma_size               10
% 1.01/0.91  
% 1.01/0.91  ------ AIG Options
% 1.01/0.91  
% 1.01/0.91  --aig_mode                              false
% 1.01/0.91  
% 1.01/0.91  ------ Instantiation Options
% 1.01/0.91  
% 1.01/0.91  --instantiation_flag                    true
% 1.01/0.91  --inst_sos_flag                         false
% 1.01/0.91  --inst_sos_phase                        true
% 1.01/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/0.91  --inst_lit_sel_side                     num_symb
% 1.01/0.91  --inst_solver_per_active                1400
% 1.01/0.91  --inst_solver_calls_frac                1.
% 1.01/0.91  --inst_passive_queue_type               priority_queues
% 1.01/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/0.91  --inst_passive_queues_freq              [25;2]
% 1.01/0.91  --inst_dismatching                      true
% 1.01/0.91  --inst_eager_unprocessed_to_passive     true
% 1.01/0.91  --inst_prop_sim_given                   true
% 1.01/0.91  --inst_prop_sim_new                     false
% 1.01/0.91  --inst_subs_new                         false
% 1.01/0.91  --inst_eq_res_simp                      false
% 1.01/0.91  --inst_subs_given                       false
% 1.01/0.91  --inst_orphan_elimination               true
% 1.01/0.91  --inst_learning_loop_flag               true
% 1.01/0.91  --inst_learning_start                   3000
% 1.01/0.91  --inst_learning_factor                  2
% 1.01/0.91  --inst_start_prop_sim_after_learn       3
% 1.01/0.91  --inst_sel_renew                        solver
% 1.01/0.91  --inst_lit_activity_flag                true
% 1.01/0.91  --inst_restr_to_given                   false
% 1.01/0.91  --inst_activity_threshold               500
% 1.01/0.91  --inst_out_proof                        true
% 1.01/0.91  
% 1.01/0.91  ------ Resolution Options
% 1.01/0.91  
% 1.01/0.91  --resolution_flag                       true
% 1.01/0.91  --res_lit_sel                           adaptive
% 1.01/0.91  --res_lit_sel_side                      none
% 1.01/0.91  --res_ordering                          kbo
% 1.01/0.91  --res_to_prop_solver                    active
% 1.01/0.91  --res_prop_simpl_new                    false
% 1.01/0.91  --res_prop_simpl_given                  true
% 1.01/0.91  --res_passive_queue_type                priority_queues
% 1.01/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/0.91  --res_passive_queues_freq               [15;5]
% 1.01/0.91  --res_forward_subs                      full
% 1.01/0.91  --res_backward_subs                     full
% 1.01/0.91  --res_forward_subs_resolution           true
% 1.01/0.91  --res_backward_subs_resolution          true
% 1.01/0.91  --res_orphan_elimination                true
% 1.01/0.91  --res_time_limit                        2.
% 1.01/0.91  --res_out_proof                         true
% 1.01/0.91  
% 1.01/0.91  ------ Superposition Options
% 1.01/0.91  
% 1.01/0.91  --superposition_flag                    true
% 1.01/0.91  --sup_passive_queue_type                priority_queues
% 1.01/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/0.91  --sup_passive_queues_freq               [8;1;4]
% 1.01/0.91  --demod_completeness_check              fast
% 1.01/0.91  --demod_use_ground                      true
% 1.01/0.91  --sup_to_prop_solver                    passive
% 1.01/0.91  --sup_prop_simpl_new                    true
% 1.01/0.91  --sup_prop_simpl_given                  true
% 1.01/0.91  --sup_fun_splitting                     false
% 1.01/0.91  --sup_smt_interval                      50000
% 1.01/0.91  
% 1.01/0.91  ------ Superposition Simplification Setup
% 1.01/0.91  
% 1.01/0.91  --sup_indices_passive                   []
% 1.01/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.91  --sup_full_bw                           [BwDemod]
% 1.01/0.91  --sup_immed_triv                        [TrivRules]
% 1.01/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.91  --sup_immed_bw_main                     []
% 1.01/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.91  
% 1.01/0.91  ------ Combination Options
% 1.01/0.91  
% 1.01/0.91  --comb_res_mult                         3
% 1.01/0.91  --comb_sup_mult                         2
% 1.01/0.91  --comb_inst_mult                        10
% 1.01/0.91  
% 1.01/0.91  ------ Debug Options
% 1.01/0.91  
% 1.01/0.91  --dbg_backtrace                         false
% 1.01/0.91  --dbg_dump_prop_clauses                 false
% 1.01/0.91  --dbg_dump_prop_clauses_file            -
% 1.01/0.91  --dbg_out_stat                          false
% 1.01/0.91  ------ Parsing...
% 1.01/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.01/0.91  
% 1.01/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.01/0.91  
% 1.01/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.01/0.91  
% 1.01/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.01/0.91  ------ Proving...
% 1.01/0.91  ------ Problem Properties 
% 1.01/0.91  
% 1.01/0.91  
% 1.01/0.91  clauses                                 10
% 1.01/0.91  conjectures                             2
% 1.01/0.91  EPR                                     0
% 1.01/0.91  Horn                                    9
% 1.01/0.91  unary                                   3
% 1.01/0.91  binary                                  2
% 1.01/0.91  lits                                    25
% 1.01/0.91  lits eq                                 12
% 1.01/0.91  fd_pure                                 0
% 1.01/0.91  fd_pseudo                               0
% 1.01/0.91  fd_cond                                 2
% 1.01/0.91  fd_pseudo_cond                          0
% 1.01/0.91  AC symbols                              0
% 1.01/0.91  
% 1.01/0.91  ------ Schedule dynamic 5 is on 
% 1.01/0.91  
% 1.01/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.01/0.91  
% 1.01/0.91  
% 1.01/0.91  ------ 
% 1.01/0.91  Current options:
% 1.01/0.91  ------ 
% 1.01/0.91  
% 1.01/0.91  ------ Input Options
% 1.01/0.91  
% 1.01/0.91  --out_options                           all
% 1.01/0.91  --tptp_safe_out                         true
% 1.01/0.91  --problem_path                          ""
% 1.01/0.91  --include_path                          ""
% 1.01/0.91  --clausifier                            res/vclausify_rel
% 1.01/0.91  --clausifier_options                    --mode clausify
% 1.01/0.91  --stdin                                 false
% 1.01/0.91  --stats_out                             all
% 1.01/0.91  
% 1.01/0.91  ------ General Options
% 1.01/0.91  
% 1.01/0.91  --fof                                   false
% 1.01/0.91  --time_out_real                         305.
% 1.01/0.91  --time_out_virtual                      -1.
% 1.01/0.91  --symbol_type_check                     false
% 1.01/0.91  --clausify_out                          false
% 1.01/0.91  --sig_cnt_out                           false
% 1.01/0.91  --trig_cnt_out                          false
% 1.01/0.91  --trig_cnt_out_tolerance                1.
% 1.01/0.91  --trig_cnt_out_sk_spl                   false
% 1.01/0.91  --abstr_cl_out                          false
% 1.01/0.91  
% 1.01/0.91  ------ Global Options
% 1.01/0.91  
% 1.01/0.91  --schedule                              default
% 1.01/0.91  --add_important_lit                     false
% 1.01/0.91  --prop_solver_per_cl                    1000
% 1.01/0.91  --min_unsat_core                        false
% 1.01/0.91  --soft_assumptions                      false
% 1.01/0.91  --soft_lemma_size                       3
% 1.01/0.91  --prop_impl_unit_size                   0
% 1.01/0.91  --prop_impl_unit                        []
% 1.01/0.91  --share_sel_clauses                     true
% 1.01/0.91  --reset_solvers                         false
% 1.01/0.91  --bc_imp_inh                            [conj_cone]
% 1.01/0.91  --conj_cone_tolerance                   3.
% 1.01/0.91  --extra_neg_conj                        none
% 1.01/0.91  --large_theory_mode                     true
% 1.01/0.91  --prolific_symb_bound                   200
% 1.01/0.91  --lt_threshold                          2000
% 1.01/0.91  --clause_weak_htbl                      true
% 1.01/0.91  --gc_record_bc_elim                     false
% 1.01/0.91  
% 1.01/0.91  ------ Preprocessing Options
% 1.01/0.91  
% 1.01/0.91  --preprocessing_flag                    true
% 1.01/0.91  --time_out_prep_mult                    0.1
% 1.01/0.91  --splitting_mode                        input
% 1.01/0.91  --splitting_grd                         true
% 1.01/0.91  --splitting_cvd                         false
% 1.01/0.91  --splitting_cvd_svl                     false
% 1.01/0.91  --splitting_nvd                         32
% 1.01/0.91  --sub_typing                            true
% 1.01/0.91  --prep_gs_sim                           true
% 1.01/0.91  --prep_unflatten                        true
% 1.01/0.91  --prep_res_sim                          true
% 1.01/0.91  --prep_upred                            true
% 1.01/0.91  --prep_sem_filter                       exhaustive
% 1.01/0.91  --prep_sem_filter_out                   false
% 1.01/0.91  --pred_elim                             true
% 1.01/0.91  --res_sim_input                         true
% 1.01/0.91  --eq_ax_congr_red                       true
% 1.01/0.91  --pure_diseq_elim                       true
% 1.01/0.91  --brand_transform                       false
% 1.01/0.91  --non_eq_to_eq                          false
% 1.01/0.91  --prep_def_merge                        true
% 1.01/0.91  --prep_def_merge_prop_impl              false
% 1.01/0.91  --prep_def_merge_mbd                    true
% 1.01/0.91  --prep_def_merge_tr_red                 false
% 1.01/0.91  --prep_def_merge_tr_cl                  false
% 1.01/0.91  --smt_preprocessing                     true
% 1.01/0.91  --smt_ac_axioms                         fast
% 1.01/0.91  --preprocessed_out                      false
% 1.01/0.91  --preprocessed_stats                    false
% 1.01/0.91  
% 1.01/0.91  ------ Abstraction refinement Options
% 1.01/0.91  
% 1.01/0.91  --abstr_ref                             []
% 1.01/0.91  --abstr_ref_prep                        false
% 1.01/0.91  --abstr_ref_until_sat                   false
% 1.01/0.91  --abstr_ref_sig_restrict                funpre
% 1.01/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/0.91  --abstr_ref_under                       []
% 1.01/0.91  
% 1.01/0.91  ------ SAT Options
% 1.01/0.91  
% 1.01/0.91  --sat_mode                              false
% 1.01/0.91  --sat_fm_restart_options                ""
% 1.01/0.91  --sat_gr_def                            false
% 1.01/0.91  --sat_epr_types                         true
% 1.01/0.91  --sat_non_cyclic_types                  false
% 1.01/0.91  --sat_finite_models                     false
% 1.01/0.91  --sat_fm_lemmas                         false
% 1.01/0.91  --sat_fm_prep                           false
% 1.01/0.91  --sat_fm_uc_incr                        true
% 1.01/0.91  --sat_out_model                         small
% 1.01/0.91  --sat_out_clauses                       false
% 1.01/0.91  
% 1.01/0.91  ------ QBF Options
% 1.01/0.91  
% 1.01/0.91  --qbf_mode                              false
% 1.01/0.91  --qbf_elim_univ                         false
% 1.01/0.91  --qbf_dom_inst                          none
% 1.01/0.91  --qbf_dom_pre_inst                      false
% 1.01/0.91  --qbf_sk_in                             false
% 1.01/0.91  --qbf_pred_elim                         true
% 1.01/0.91  --qbf_split                             512
% 1.01/0.91  
% 1.01/0.91  ------ BMC1 Options
% 1.01/0.91  
% 1.01/0.91  --bmc1_incremental                      false
% 1.01/0.91  --bmc1_axioms                           reachable_all
% 1.01/0.91  --bmc1_min_bound                        0
% 1.01/0.91  --bmc1_max_bound                        -1
% 1.01/0.91  --bmc1_max_bound_default                -1
% 1.01/0.91  --bmc1_symbol_reachability              true
% 1.01/0.91  --bmc1_property_lemmas                  false
% 1.01/0.91  --bmc1_k_induction                      false
% 1.01/0.91  --bmc1_non_equiv_states                 false
% 1.01/0.91  --bmc1_deadlock                         false
% 1.01/0.91  --bmc1_ucm                              false
% 1.01/0.91  --bmc1_add_unsat_core                   none
% 1.01/0.91  --bmc1_unsat_core_children              false
% 1.01/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/0.91  --bmc1_out_stat                         full
% 1.01/0.91  --bmc1_ground_init                      false
% 1.01/0.91  --bmc1_pre_inst_next_state              false
% 1.01/0.91  --bmc1_pre_inst_state                   false
% 1.01/0.91  --bmc1_pre_inst_reach_state             false
% 1.01/0.91  --bmc1_out_unsat_core                   false
% 1.01/0.91  --bmc1_aig_witness_out                  false
% 1.01/0.91  --bmc1_verbose                          false
% 1.01/0.91  --bmc1_dump_clauses_tptp                false
% 1.01/0.91  --bmc1_dump_unsat_core_tptp             false
% 1.01/0.91  --bmc1_dump_file                        -
% 1.01/0.91  --bmc1_ucm_expand_uc_limit              128
% 1.01/0.91  --bmc1_ucm_n_expand_iterations          6
% 1.01/0.91  --bmc1_ucm_extend_mode                  1
% 1.01/0.91  --bmc1_ucm_init_mode                    2
% 1.01/0.91  --bmc1_ucm_cone_mode                    none
% 1.01/0.91  --bmc1_ucm_reduced_relation_type        0
% 1.01/0.91  --bmc1_ucm_relax_model                  4
% 1.01/0.91  --bmc1_ucm_full_tr_after_sat            true
% 1.01/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/0.91  --bmc1_ucm_layered_model                none
% 1.01/0.91  --bmc1_ucm_max_lemma_size               10
% 1.01/0.91  
% 1.01/0.91  ------ AIG Options
% 1.01/0.91  
% 1.01/0.91  --aig_mode                              false
% 1.01/0.91  
% 1.01/0.91  ------ Instantiation Options
% 1.01/0.91  
% 1.01/0.91  --instantiation_flag                    true
% 1.01/0.91  --inst_sos_flag                         false
% 1.01/0.91  --inst_sos_phase                        true
% 1.01/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/0.91  --inst_lit_sel_side                     none
% 1.01/0.91  --inst_solver_per_active                1400
% 1.01/0.91  --inst_solver_calls_frac                1.
% 1.01/0.91  --inst_passive_queue_type               priority_queues
% 1.01/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/0.91  --inst_passive_queues_freq              [25;2]
% 1.01/0.91  --inst_dismatching                      true
% 1.01/0.91  --inst_eager_unprocessed_to_passive     true
% 1.01/0.91  --inst_prop_sim_given                   true
% 1.01/0.91  --inst_prop_sim_new                     false
% 1.01/0.91  --inst_subs_new                         false
% 1.01/0.91  --inst_eq_res_simp                      false
% 1.01/0.91  --inst_subs_given                       false
% 1.01/0.91  --inst_orphan_elimination               true
% 1.01/0.91  --inst_learning_loop_flag               true
% 1.01/0.91  --inst_learning_start                   3000
% 1.01/0.91  --inst_learning_factor                  2
% 1.01/0.91  --inst_start_prop_sim_after_learn       3
% 1.01/0.91  --inst_sel_renew                        solver
% 1.01/0.91  --inst_lit_activity_flag                true
% 1.01/0.91  --inst_restr_to_given                   false
% 1.01/0.91  --inst_activity_threshold               500
% 1.01/0.91  --inst_out_proof                        true
% 1.01/0.91  
% 1.01/0.91  ------ Resolution Options
% 1.01/0.91  
% 1.01/0.91  --resolution_flag                       false
% 1.01/0.91  --res_lit_sel                           adaptive
% 1.01/0.91  --res_lit_sel_side                      none
% 1.01/0.91  --res_ordering                          kbo
% 1.01/0.91  --res_to_prop_solver                    active
% 1.01/0.91  --res_prop_simpl_new                    false
% 1.01/0.91  --res_prop_simpl_given                  true
% 1.01/0.91  --res_passive_queue_type                priority_queues
% 1.01/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/0.91  --res_passive_queues_freq               [15;5]
% 1.01/0.91  --res_forward_subs                      full
% 1.01/0.91  --res_backward_subs                     full
% 1.01/0.91  --res_forward_subs_resolution           true
% 1.01/0.91  --res_backward_subs_resolution          true
% 1.01/0.91  --res_orphan_elimination                true
% 1.01/0.91  --res_time_limit                        2.
% 1.01/0.91  --res_out_proof                         true
% 1.01/0.91  
% 1.01/0.91  ------ Superposition Options
% 1.01/0.91  
% 1.01/0.91  --superposition_flag                    true
% 1.01/0.91  --sup_passive_queue_type                priority_queues
% 1.01/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/0.91  --sup_passive_queues_freq               [8;1;4]
% 1.01/0.91  --demod_completeness_check              fast
% 1.01/0.91  --demod_use_ground                      true
% 1.01/0.91  --sup_to_prop_solver                    passive
% 1.01/0.91  --sup_prop_simpl_new                    true
% 1.01/0.91  --sup_prop_simpl_given                  true
% 1.01/0.91  --sup_fun_splitting                     false
% 1.01/0.91  --sup_smt_interval                      50000
% 1.01/0.91  
% 1.01/0.91  ------ Superposition Simplification Setup
% 1.01/0.91  
% 1.01/0.91  --sup_indices_passive                   []
% 1.01/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.91  --sup_full_bw                           [BwDemod]
% 1.01/0.91  --sup_immed_triv                        [TrivRules]
% 1.01/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.91  --sup_immed_bw_main                     []
% 1.01/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.91  
% 1.01/0.91  ------ Combination Options
% 1.01/0.91  
% 1.01/0.91  --comb_res_mult                         3
% 1.01/0.91  --comb_sup_mult                         2
% 1.01/0.91  --comb_inst_mult                        10
% 1.01/0.91  
% 1.01/0.91  ------ Debug Options
% 1.01/0.91  
% 1.01/0.91  --dbg_backtrace                         false
% 1.01/0.91  --dbg_dump_prop_clauses                 false
% 1.01/0.91  --dbg_dump_prop_clauses_file            -
% 1.01/0.91  --dbg_out_stat                          false
% 1.01/0.91  
% 1.01/0.91  
% 1.01/0.91  
% 1.01/0.91  
% 1.01/0.91  ------ Proving...
% 1.01/0.91  
% 1.01/0.91  
% 1.01/0.91  % SZS status Theorem for theBenchmark.p
% 1.01/0.91  
% 1.01/0.91  % SZS output start CNFRefutation for theBenchmark.p
% 1.01/0.91  
% 1.01/0.91  fof(f8,conjecture,(
% 1.01/0.91    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 1.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.91  
% 1.01/0.91  fof(f9,negated_conjecture,(
% 1.01/0.91    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 1.01/0.91    inference(negated_conjecture,[],[f8])).
% 1.01/0.91  
% 1.01/0.91  fof(f26,plain,(
% 1.01/0.91    ? [X0] : (? [X1] : (k3_lattices(X0,k5_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.01/0.91    inference(ennf_transformation,[],[f9])).
% 1.01/0.91  
% 1.01/0.91  fof(f27,plain,(
% 1.01/0.91    ? [X0] : (? [X1] : (k3_lattices(X0,k5_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.01/0.91    inference(flattening,[],[f26])).
% 1.01/0.91  
% 1.01/0.91  fof(f35,plain,(
% 1.01/0.91    ( ! [X0] : (? [X1] : (k3_lattices(X0,k5_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) => (k3_lattices(X0,k5_lattices(X0),sK2) != sK2 & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.01/0.91    introduced(choice_axiom,[])).
% 1.01/0.91  
% 1.01/0.91  fof(f34,plain,(
% 1.01/0.91    ? [X0] : (? [X1] : (k3_lattices(X0,k5_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k3_lattices(sK1,k5_lattices(sK1),X1) != X1 & m1_subset_1(X1,u1_struct_0(sK1))) & l3_lattices(sK1) & v13_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 1.01/0.91    introduced(choice_axiom,[])).
% 1.01/0.91  
% 1.01/0.91  fof(f36,plain,(
% 1.01/0.91    (k3_lattices(sK1,k5_lattices(sK1),sK2) != sK2 & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v13_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 1.01/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f35,f34])).
% 1.01/0.91  
% 1.01/0.91  fof(f54,plain,(
% 1.01/0.91    v10_lattices(sK1)),
% 1.01/0.91    inference(cnf_transformation,[],[f36])).
% 1.01/0.91  
% 1.01/0.91  fof(f1,axiom,(
% 1.01/0.91    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.91  
% 1.01/0.91  fof(f10,plain,(
% 1.01/0.91    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/0.91    inference(pure_predicate_removal,[],[f1])).
% 1.01/0.91  
% 1.01/0.91  fof(f11,plain,(
% 1.01/0.91    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/0.91    inference(pure_predicate_removal,[],[f10])).
% 1.01/0.91  
% 1.01/0.91  fof(f12,plain,(
% 1.01/0.91    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/0.91    inference(pure_predicate_removal,[],[f11])).
% 1.01/0.91  
% 1.01/0.91  fof(f13,plain,(
% 1.01/0.91    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.01/0.91    inference(ennf_transformation,[],[f12])).
% 1.01/0.91  
% 1.01/0.91  fof(f14,plain,(
% 1.01/0.91    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.01/0.91    inference(flattening,[],[f13])).
% 1.01/0.91  
% 1.01/0.91  fof(f38,plain,(
% 1.01/0.91    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f14])).
% 1.01/0.91  
% 1.01/0.91  fof(f6,axiom,(
% 1.01/0.91    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 1.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.91  
% 1.01/0.91  fof(f22,plain,(
% 1.01/0.91    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.01/0.91    inference(ennf_transformation,[],[f6])).
% 1.01/0.91  
% 1.01/0.91  fof(f23,plain,(
% 1.01/0.91    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(flattening,[],[f22])).
% 1.01/0.91  
% 1.01/0.91  fof(f50,plain,(
% 1.01/0.91    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f23])).
% 1.01/0.91  
% 1.01/0.91  fof(f5,axiom,(
% 1.01/0.91    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.91  
% 1.01/0.91  fof(f21,plain,(
% 1.01/0.91    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.01/0.91    inference(ennf_transformation,[],[f5])).
% 1.01/0.91  
% 1.01/0.91  fof(f49,plain,(
% 1.01/0.91    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f21])).
% 1.01/0.91  
% 1.01/0.91  fof(f53,plain,(
% 1.01/0.91    ~v2_struct_0(sK1)),
% 1.01/0.91    inference(cnf_transformation,[],[f36])).
% 1.01/0.91  
% 1.01/0.91  fof(f56,plain,(
% 1.01/0.91    l3_lattices(sK1)),
% 1.01/0.91    inference(cnf_transformation,[],[f36])).
% 1.01/0.91  
% 1.01/0.91  fof(f7,axiom,(
% 1.01/0.91    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.91  
% 1.01/0.91  fof(f24,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.01/0.91    inference(ennf_transformation,[],[f7])).
% 1.01/0.91  
% 1.01/0.91  fof(f25,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(flattening,[],[f24])).
% 1.01/0.91  
% 1.01/0.91  fof(f33,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(nnf_transformation,[],[f25])).
% 1.01/0.91  
% 1.01/0.91  fof(f52,plain,(
% 1.01/0.91    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f33])).
% 1.01/0.91  
% 1.01/0.91  fof(f40,plain,(
% 1.01/0.91    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f14])).
% 1.01/0.91  
% 1.01/0.91  fof(f39,plain,(
% 1.01/0.91    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f14])).
% 1.01/0.91  
% 1.01/0.91  fof(f3,axiom,(
% 1.01/0.91    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 1.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.91  
% 1.01/0.91  fof(f17,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.01/0.91    inference(ennf_transformation,[],[f3])).
% 1.01/0.91  
% 1.01/0.91  fof(f18,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(flattening,[],[f17])).
% 1.01/0.91  
% 1.01/0.91  fof(f32,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(nnf_transformation,[],[f18])).
% 1.01/0.91  
% 1.01/0.91  fof(f45,plain,(
% 1.01/0.91    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f32])).
% 1.01/0.91  
% 1.01/0.91  fof(f2,axiom,(
% 1.01/0.91    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 1.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.91  
% 1.01/0.91  fof(f15,plain,(
% 1.01/0.91    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.01/0.91    inference(ennf_transformation,[],[f2])).
% 1.01/0.91  
% 1.01/0.91  fof(f16,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(flattening,[],[f15])).
% 1.01/0.91  
% 1.01/0.91  fof(f28,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(nnf_transformation,[],[f16])).
% 1.01/0.91  
% 1.01/0.91  fof(f29,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(rectify,[],[f28])).
% 1.01/0.91  
% 1.01/0.91  fof(f30,plain,(
% 1.01/0.91    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 1.01/0.91    introduced(choice_axiom,[])).
% 1.01/0.91  
% 1.01/0.91  fof(f31,plain,(
% 1.01/0.91    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 1.01/0.91  
% 1.01/0.91  fof(f41,plain,(
% 1.01/0.91    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f31])).
% 1.01/0.91  
% 1.01/0.91  fof(f60,plain,(
% 1.01/0.91    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/0.91    inference(equality_resolution,[],[f41])).
% 1.01/0.91  
% 1.01/0.91  fof(f55,plain,(
% 1.01/0.91    v13_lattices(sK1)),
% 1.01/0.91    inference(cnf_transformation,[],[f36])).
% 1.01/0.91  
% 1.01/0.91  fof(f48,plain,(
% 1.01/0.91    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f21])).
% 1.01/0.91  
% 1.01/0.91  fof(f4,axiom,(
% 1.01/0.91    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 1.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.91  
% 1.01/0.91  fof(f19,plain,(
% 1.01/0.91    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.01/0.91    inference(ennf_transformation,[],[f4])).
% 1.01/0.91  
% 1.01/0.91  fof(f20,plain,(
% 1.01/0.91    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.01/0.91    inference(flattening,[],[f19])).
% 1.01/0.91  
% 1.01/0.91  fof(f47,plain,(
% 1.01/0.91    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/0.91    inference(cnf_transformation,[],[f20])).
% 1.01/0.91  
% 1.01/0.91  fof(f58,plain,(
% 1.01/0.91    k3_lattices(sK1,k5_lattices(sK1),sK2) != sK2),
% 1.01/0.91    inference(cnf_transformation,[],[f36])).
% 1.01/0.91  
% 1.01/0.91  fof(f57,plain,(
% 1.01/0.91    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.01/0.91    inference(cnf_transformation,[],[f36])).
% 1.01/0.91  
% 1.01/0.91  cnf(c_734,plain,
% 1.01/0.91      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 1.01/0.91      theory(equality) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_1038,plain,
% 1.01/0.91      ( k1_lattices(sK1,k5_lattices(sK1),sK2) != X0_47
% 1.01/0.91      | sK2 != X0_47
% 1.01/0.91      | sK2 = k1_lattices(sK1,k5_lattices(sK1),sK2) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_734]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_1039,plain,
% 1.01/0.91      ( k1_lattices(sK1,k5_lattices(sK1),sK2) != sK2
% 1.01/0.91      | sK2 = k1_lattices(sK1,k5_lattices(sK1),sK2)
% 1.01/0.91      | sK2 != sK2 ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_1038]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_20,negated_conjecture,
% 1.01/0.91      ( v10_lattices(sK1) ),
% 1.01/0.91      inference(cnf_transformation,[],[f54]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_2,plain,
% 1.01/0.91      ( v4_lattices(X0)
% 1.01/0.91      | ~ l3_lattices(X0)
% 1.01/0.91      | v2_struct_0(X0)
% 1.01/0.91      | ~ v10_lattices(X0) ),
% 1.01/0.91      inference(cnf_transformation,[],[f38]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_13,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/0.91      | ~ l2_lattices(X1)
% 1.01/0.91      | ~ v4_lattices(X1)
% 1.01/0.91      | v2_struct_0(X1)
% 1.01/0.91      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
% 1.01/0.91      inference(cnf_transformation,[],[f50]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_229,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/0.91      | ~ l2_lattices(X1)
% 1.01/0.91      | ~ l3_lattices(X3)
% 1.01/0.91      | v2_struct_0(X3)
% 1.01/0.91      | v2_struct_0(X1)
% 1.01/0.91      | ~ v10_lattices(X3)
% 1.01/0.91      | X1 != X3
% 1.01/0.91      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
% 1.01/0.91      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_230,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/0.91      | ~ l2_lattices(X1)
% 1.01/0.91      | ~ l3_lattices(X1)
% 1.01/0.91      | v2_struct_0(X1)
% 1.01/0.91      | ~ v10_lattices(X1)
% 1.01/0.91      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
% 1.01/0.91      inference(unflattening,[status(thm)],[c_229]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_11,plain,
% 1.01/0.91      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 1.01/0.91      inference(cnf_transformation,[],[f49]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_248,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/0.91      | ~ l3_lattices(X1)
% 1.01/0.91      | v2_struct_0(X1)
% 1.01/0.91      | ~ v10_lattices(X1)
% 1.01/0.91      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
% 1.01/0.91      inference(forward_subsumption_resolution,
% 1.01/0.91                [status(thm)],
% 1.01/0.91                [c_230,c_11]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_287,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/0.91      | ~ l3_lattices(X1)
% 1.01/0.91      | v2_struct_0(X1)
% 1.01/0.91      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
% 1.01/0.91      | sK1 != X1 ),
% 1.01/0.91      inference(resolution_lifted,[status(thm)],[c_20,c_248]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_288,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.01/0.91      | ~ l3_lattices(sK1)
% 1.01/0.91      | v2_struct_0(sK1)
% 1.01/0.91      | k3_lattices(sK1,X1,X0) = k1_lattices(sK1,X1,X0) ),
% 1.01/0.91      inference(unflattening,[status(thm)],[c_287]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_21,negated_conjecture,
% 1.01/0.91      ( ~ v2_struct_0(sK1) ),
% 1.01/0.91      inference(cnf_transformation,[],[f53]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_18,negated_conjecture,
% 1.01/0.91      ( l3_lattices(sK1) ),
% 1.01/0.91      inference(cnf_transformation,[],[f56]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_292,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.01/0.91      | k3_lattices(sK1,X1,X0) = k1_lattices(sK1,X1,X0) ),
% 1.01/0.91      inference(global_propositional_subsumption,
% 1.01/0.91                [status(thm)],
% 1.01/0.91                [c_288,c_21,c_18]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_729,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0_47,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X1_47,u1_struct_0(sK1))
% 1.01/0.91      | k3_lattices(sK1,X1_47,X0_47) = k1_lattices(sK1,X1_47,X0_47) ),
% 1.01/0.91      inference(subtyping,[status(esa)],[c_292]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_1009,plain,
% 1.01/0.91      ( ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.01/0.91      | k3_lattices(sK1,k5_lattices(sK1),sK2) = k1_lattices(sK1,k5_lattices(sK1),sK2) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_729]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_994,plain,
% 1.01/0.91      ( k3_lattices(sK1,k5_lattices(sK1),sK2) != X0_47
% 1.01/0.91      | k3_lattices(sK1,k5_lattices(sK1),sK2) = sK2
% 1.01/0.91      | sK2 != X0_47 ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_734]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_1008,plain,
% 1.01/0.91      ( k3_lattices(sK1,k5_lattices(sK1),sK2) != k1_lattices(sK1,k5_lattices(sK1),sK2)
% 1.01/0.91      | k3_lattices(sK1,k5_lattices(sK1),sK2) = sK2
% 1.01/0.91      | sK2 != k1_lattices(sK1,k5_lattices(sK1),sK2) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_994]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_14,plain,
% 1.01/0.91      ( r1_lattices(X0,X1,X2)
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/0.91      | ~ v8_lattices(X0)
% 1.01/0.91      | ~ l3_lattices(X0)
% 1.01/0.91      | v2_struct_0(X0)
% 1.01/0.91      | ~ v9_lattices(X0)
% 1.01/0.91      | k2_lattices(X0,X1,X2) != X1 ),
% 1.01/0.91      inference(cnf_transformation,[],[f52]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_0,plain,
% 1.01/0.91      ( ~ l3_lattices(X0)
% 1.01/0.91      | v2_struct_0(X0)
% 1.01/0.91      | ~ v10_lattices(X0)
% 1.01/0.91      | v9_lattices(X0) ),
% 1.01/0.91      inference(cnf_transformation,[],[f40]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_276,plain,
% 1.01/0.91      ( ~ l3_lattices(X0)
% 1.01/0.91      | v2_struct_0(X0)
% 1.01/0.91      | v9_lattices(X0)
% 1.01/0.91      | sK1 != X0 ),
% 1.01/0.91      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_277,plain,
% 1.01/0.91      ( ~ l3_lattices(sK1) | v2_struct_0(sK1) | v9_lattices(sK1) ),
% 1.01/0.91      inference(unflattening,[status(thm)],[c_276]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_71,plain,
% 1.01/0.91      ( ~ l3_lattices(sK1)
% 1.01/0.91      | v2_struct_0(sK1)
% 1.01/0.91      | ~ v10_lattices(sK1)
% 1.01/0.91      | v9_lattices(sK1) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_0]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_279,plain,
% 1.01/0.91      ( v9_lattices(sK1) ),
% 1.01/0.91      inference(global_propositional_subsumption,
% 1.01/0.91                [status(thm)],
% 1.01/0.91                [c_277,c_21,c_20,c_18,c_71]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_400,plain,
% 1.01/0.91      ( r1_lattices(X0,X1,X2)
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/0.91      | ~ v8_lattices(X0)
% 1.01/0.91      | ~ l3_lattices(X0)
% 1.01/0.91      | v2_struct_0(X0)
% 1.01/0.91      | k2_lattices(X0,X1,X2) != X1
% 1.01/0.91      | sK1 != X0 ),
% 1.01/0.91      inference(resolution_lifted,[status(thm)],[c_14,c_279]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_401,plain,
% 1.01/0.91      ( r1_lattices(sK1,X0,X1)
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | ~ v8_lattices(sK1)
% 1.01/0.91      | ~ l3_lattices(sK1)
% 1.01/0.91      | v2_struct_0(sK1)
% 1.01/0.91      | k2_lattices(sK1,X0,X1) != X0 ),
% 1.01/0.91      inference(unflattening,[status(thm)],[c_400]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_1,plain,
% 1.01/0.91      ( v8_lattices(X0)
% 1.01/0.91      | ~ l3_lattices(X0)
% 1.01/0.91      | v2_struct_0(X0)
% 1.01/0.91      | ~ v10_lattices(X0) ),
% 1.01/0.91      inference(cnf_transformation,[],[f39]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_68,plain,
% 1.01/0.91      ( v8_lattices(sK1)
% 1.01/0.91      | ~ l3_lattices(sK1)
% 1.01/0.91      | v2_struct_0(sK1)
% 1.01/0.91      | ~ v10_lattices(sK1) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_1]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_405,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.01/0.91      | r1_lattices(sK1,X0,X1)
% 1.01/0.91      | k2_lattices(sK1,X0,X1) != X0 ),
% 1.01/0.91      inference(global_propositional_subsumption,
% 1.01/0.91                [status(thm)],
% 1.01/0.91                [c_401,c_21,c_20,c_18,c_68]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_406,plain,
% 1.01/0.91      ( r1_lattices(sK1,X0,X1)
% 1.01/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.01/0.91      | k2_lattices(sK1,X0,X1) != X0 ),
% 1.01/0.91      inference(renaming,[status(thm)],[c_405]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_9,plain,
% 1.01/0.91      ( ~ r1_lattices(X0,X1,X2)
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/0.91      | ~ l2_lattices(X0)
% 1.01/0.91      | v2_struct_0(X0)
% 1.01/0.91      | k1_lattices(X0,X1,X2) = X2 ),
% 1.01/0.91      inference(cnf_transformation,[],[f45]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_316,plain,
% 1.01/0.91      ( ~ r1_lattices(X0,X1,X2)
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/0.91      | ~ l3_lattices(X0)
% 1.01/0.91      | v2_struct_0(X0)
% 1.01/0.91      | k1_lattices(X0,X1,X2) = X2 ),
% 1.01/0.91      inference(resolution,[status(thm)],[c_11,c_9]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_458,plain,
% 1.01/0.91      ( ~ r1_lattices(X0,X1,X2)
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/0.91      | v2_struct_0(X0)
% 1.01/0.91      | k1_lattices(X0,X1,X2) = X2
% 1.01/0.91      | sK1 != X0 ),
% 1.01/0.91      inference(resolution_lifted,[status(thm)],[c_316,c_18]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_459,plain,
% 1.01/0.91      ( ~ r1_lattices(sK1,X0,X1)
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | v2_struct_0(sK1)
% 1.01/0.91      | k1_lattices(sK1,X0,X1) = X1 ),
% 1.01/0.91      inference(unflattening,[status(thm)],[c_458]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_463,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.01/0.91      | ~ r1_lattices(sK1,X0,X1)
% 1.01/0.91      | k1_lattices(sK1,X0,X1) = X1 ),
% 1.01/0.91      inference(global_propositional_subsumption,
% 1.01/0.91                [status(thm)],
% 1.01/0.91                [c_459,c_21]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_464,plain,
% 1.01/0.91      ( ~ r1_lattices(sK1,X0,X1)
% 1.01/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.01/0.91      | k1_lattices(sK1,X0,X1) = X1 ),
% 1.01/0.91      inference(renaming,[status(thm)],[c_463]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_628,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.01/0.91      | k1_lattices(sK1,X0,X1) = X1
% 1.01/0.91      | k2_lattices(sK1,X0,X1) != X0 ),
% 1.01/0.91      inference(resolution,[status(thm)],[c_406,c_464]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_722,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0_47,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(X1_47,u1_struct_0(sK1))
% 1.01/0.91      | k1_lattices(sK1,X0_47,X1_47) = X1_47
% 1.01/0.91      | k2_lattices(sK1,X0_47,X1_47) != X0_47 ),
% 1.01/0.91      inference(subtyping,[status(esa)],[c_628]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_984,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0_47,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 1.01/0.91      | k1_lattices(sK1,k5_lattices(sK1),X0_47) = X0_47
% 1.01/0.91      | k2_lattices(sK1,k5_lattices(sK1),X0_47) != k5_lattices(sK1) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_722]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_986,plain,
% 1.01/0.91      ( ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.01/0.91      | k1_lattices(sK1,k5_lattices(sK1),sK2) = sK2
% 1.01/0.91      | k2_lattices(sK1,k5_lattices(sK1),sK2) != k5_lattices(sK1) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_984]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_7,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/0.91      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 1.01/0.91      | ~ l1_lattices(X1)
% 1.01/0.91      | ~ v13_lattices(X1)
% 1.01/0.91      | v2_struct_0(X1)
% 1.01/0.91      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
% 1.01/0.91      inference(cnf_transformation,[],[f60]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_19,negated_conjecture,
% 1.01/0.91      ( v13_lattices(sK1) ),
% 1.01/0.91      inference(cnf_transformation,[],[f55]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_501,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/0.91      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 1.01/0.91      | ~ l1_lattices(X1)
% 1.01/0.91      | v2_struct_0(X1)
% 1.01/0.91      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
% 1.01/0.91      | sK1 != X1 ),
% 1.01/0.91      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_502,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 1.01/0.91      | ~ l1_lattices(sK1)
% 1.01/0.91      | v2_struct_0(sK1)
% 1.01/0.91      | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
% 1.01/0.91      inference(unflattening,[status(thm)],[c_501]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_12,plain,
% 1.01/0.91      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 1.01/0.91      inference(cnf_transformation,[],[f48]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_37,plain,
% 1.01/0.91      ( l1_lattices(sK1) | ~ l3_lattices(sK1) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_12]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_10,plain,
% 1.01/0.91      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 1.01/0.91      | ~ l1_lattices(X0)
% 1.01/0.91      | v2_struct_0(X0) ),
% 1.01/0.91      inference(cnf_transformation,[],[f47]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_43,plain,
% 1.01/0.91      ( m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
% 1.01/0.91      | ~ l1_lattices(sK1)
% 1.01/0.91      | v2_struct_0(sK1) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_10]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_506,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.01/0.91      | k2_lattices(sK1,k5_lattices(sK1),X0) = k5_lattices(sK1) ),
% 1.01/0.91      inference(global_propositional_subsumption,
% 1.01/0.91                [status(thm)],
% 1.01/0.91                [c_502,c_21,c_18,c_37,c_43]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_728,plain,
% 1.01/0.91      ( ~ m1_subset_1(X0_47,u1_struct_0(sK1))
% 1.01/0.91      | k2_lattices(sK1,k5_lattices(sK1),X0_47) = k5_lattices(sK1) ),
% 1.01/0.91      inference(subtyping,[status(esa)],[c_506]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_748,plain,
% 1.01/0.91      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.01/0.91      | k2_lattices(sK1,k5_lattices(sK1),sK2) = k5_lattices(sK1) ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_728]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_16,negated_conjecture,
% 1.01/0.91      ( k3_lattices(sK1,k5_lattices(sK1),sK2) != sK2 ),
% 1.01/0.91      inference(cnf_transformation,[],[f58]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_731,negated_conjecture,
% 1.01/0.91      ( k3_lattices(sK1,k5_lattices(sK1),sK2) != sK2 ),
% 1.01/0.91      inference(subtyping,[status(esa)],[c_16]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_733,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_742,plain,
% 1.01/0.91      ( sK2 = sK2 ),
% 1.01/0.91      inference(instantiation,[status(thm)],[c_733]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(c_17,negated_conjecture,
% 1.01/0.91      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.01/0.91      inference(cnf_transformation,[],[f57]) ).
% 1.01/0.91  
% 1.01/0.91  cnf(contradiction,plain,
% 1.01/0.91      ( $false ),
% 1.01/0.91      inference(minisat,
% 1.01/0.91                [status(thm)],
% 1.01/0.91                [c_1039,c_1009,c_1008,c_986,c_748,c_731,c_742,c_43,c_37,
% 1.01/0.91                 c_17,c_18,c_21]) ).
% 1.01/0.91  
% 1.01/0.91  
% 1.01/0.91  % SZS output end CNFRefutation for theBenchmark.p
% 1.01/0.91  
% 1.01/0.91  ------                               Statistics
% 1.01/0.91  
% 1.01/0.91  ------ General
% 1.01/0.91  
% 1.01/0.91  abstr_ref_over_cycles:                  0
% 1.01/0.91  abstr_ref_under_cycles:                 0
% 1.01/0.91  gc_basic_clause_elim:                   0
% 1.01/0.91  forced_gc_time:                         0
% 1.01/0.91  parsing_time:                           0.008
% 1.01/0.91  unif_index_cands_time:                  0.
% 1.01/0.91  unif_index_add_time:                    0.
% 1.01/0.91  orderings_time:                         0.
% 1.01/0.91  out_proof_time:                         0.011
% 1.01/0.91  total_time:                             0.056
% 1.01/0.91  num_of_symbols:                         50
% 1.01/0.91  num_of_terms:                           722
% 1.01/0.91  
% 1.01/0.91  ------ Preprocessing
% 1.01/0.91  
% 1.01/0.91  num_of_splits:                          0
% 1.01/0.91  num_of_split_atoms:                     0
% 1.01/0.91  num_of_reused_defs:                     0
% 1.01/0.91  num_eq_ax_congr_red:                    27
% 1.01/0.91  num_of_sem_filtered_clauses:            1
% 1.01/0.91  num_of_subtypes:                        3
% 1.01/0.91  monotx_restored_types:                  0
% 1.01/0.91  sat_num_of_epr_types:                   0
% 1.01/0.91  sat_num_of_non_cyclic_types:            0
% 1.01/0.91  sat_guarded_non_collapsed_types:        1
% 1.01/0.91  num_pure_diseq_elim:                    0
% 1.01/0.91  simp_replaced_by:                       0
% 1.01/0.91  res_preprocessed:                       62
% 1.01/0.91  prep_upred:                             0
% 1.01/0.91  prep_unflattend:                        14
% 1.01/0.91  smt_new_axioms:                         0
% 1.01/0.91  pred_elim_cands:                        1
% 1.01/0.91  pred_elim:                              10
% 1.01/0.91  pred_elim_cl:                           11
% 1.01/0.91  pred_elim_cycles:                       12
% 1.01/0.91  merged_defs:                            0
% 1.01/0.91  merged_defs_ncl:                        0
% 1.01/0.91  bin_hyper_res:                          0
% 1.01/0.91  prep_cycles:                            4
% 1.01/0.91  pred_elim_time:                         0.006
% 1.01/0.91  splitting_time:                         0.
% 1.01/0.91  sem_filter_time:                        0.
% 1.01/0.91  monotx_time:                            0.
% 1.01/0.91  subtype_inf_time:                       0.
% 1.01/0.91  
% 1.01/0.91  ------ Problem properties
% 1.01/0.91  
% 1.01/0.91  clauses:                                10
% 1.01/0.91  conjectures:                            2
% 1.01/0.91  epr:                                    0
% 1.01/0.91  horn:                                   9
% 1.01/0.91  ground:                                 3
% 1.01/0.91  unary:                                  3
% 1.01/0.91  binary:                                 2
% 1.01/0.91  lits:                                   25
% 1.01/0.91  lits_eq:                                12
% 1.01/0.91  fd_pure:                                0
% 1.01/0.91  fd_pseudo:                              0
% 1.01/0.91  fd_cond:                                2
% 1.01/0.91  fd_pseudo_cond:                         0
% 1.01/0.91  ac_symbols:                             0
% 1.01/0.91  
% 1.01/0.91  ------ Propositional Solver
% 1.01/0.91  
% 1.01/0.91  prop_solver_calls:                      23
% 1.01/0.91  prop_fast_solver_calls:                 496
% 1.01/0.91  smt_solver_calls:                       0
% 1.01/0.91  smt_fast_solver_calls:                  0
% 1.01/0.91  prop_num_of_clauses:                    260
% 1.01/0.91  prop_preprocess_simplified:             1659
% 1.01/0.91  prop_fo_subsumed:                       25
% 1.01/0.91  prop_solver_time:                       0.
% 1.01/0.91  smt_solver_time:                        0.
% 1.01/0.91  smt_fast_solver_time:                   0.
% 1.01/0.91  prop_fast_solver_time:                  0.
% 1.01/0.91  prop_unsat_core_time:                   0.
% 1.01/0.91  
% 1.01/0.91  ------ QBF
% 1.01/0.91  
% 1.01/0.91  qbf_q_res:                              0
% 1.01/0.91  qbf_num_tautologies:                    0
% 1.01/0.91  qbf_prep_cycles:                        0
% 1.01/0.91  
% 1.01/0.91  ------ BMC1
% 1.01/0.91  
% 1.01/0.91  bmc1_current_bound:                     -1
% 1.01/0.91  bmc1_last_solved_bound:                 -1
% 1.01/0.91  bmc1_unsat_core_size:                   -1
% 1.01/0.91  bmc1_unsat_core_parents_size:           -1
% 1.01/0.91  bmc1_merge_next_fun:                    0
% 1.01/0.91  bmc1_unsat_core_clauses_time:           0.
% 1.01/0.91  
% 1.01/0.91  ------ Instantiation
% 1.01/0.91  
% 1.01/0.91  inst_num_of_clauses:                    34
% 1.01/0.91  inst_num_in_passive:                    12
% 1.01/0.91  inst_num_in_active:                     19
% 1.01/0.91  inst_num_in_unprocessed:                2
% 1.01/0.91  inst_num_of_loops:                      21
% 1.01/0.91  inst_num_of_learning_restarts:          0
% 1.01/0.91  inst_num_moves_active_passive:          0
% 1.01/0.91  inst_lit_activity:                      0
% 1.01/0.91  inst_lit_activity_moves:                0
% 1.01/0.91  inst_num_tautologies:                   0
% 1.01/0.91  inst_num_prop_implied:                  0
% 1.01/0.91  inst_num_existing_simplified:           0
% 1.01/0.91  inst_num_eq_res_simplified:             0
% 1.01/0.91  inst_num_child_elim:                    0
% 1.01/0.91  inst_num_of_dismatching_blockings:      0
% 1.01/0.91  inst_num_of_non_proper_insts:           11
% 1.01/0.91  inst_num_of_duplicates:                 0
% 1.01/0.91  inst_inst_num_from_inst_to_res:         0
% 1.01/0.91  inst_dismatching_checking_time:         0.
% 1.01/0.91  
% 1.01/0.91  ------ Resolution
% 1.01/0.91  
% 1.01/0.91  res_num_of_clauses:                     0
% 1.01/0.91  res_num_in_passive:                     0
% 1.01/0.91  res_num_in_active:                      0
% 1.01/0.91  res_num_of_loops:                       66
% 1.01/0.91  res_forward_subset_subsumed:            0
% 1.01/0.91  res_backward_subset_subsumed:           0
% 1.01/0.91  res_forward_subsumed:                   0
% 1.01/0.91  res_backward_subsumed:                  0
% 1.01/0.91  res_forward_subsumption_resolution:     1
% 1.01/0.91  res_backward_subsumption_resolution:    0
% 1.01/0.91  res_clause_to_clause_subsumption:       22
% 1.01/0.91  res_orphan_elimination:                 0
% 1.01/0.91  res_tautology_del:                      3
% 1.01/0.91  res_num_eq_res_simplified:              0
% 1.01/0.91  res_num_sel_changes:                    0
% 1.01/0.91  res_moves_from_active_to_pass:          0
% 1.01/0.91  
% 1.01/0.91  ------ Superposition
% 1.01/0.91  
% 1.01/0.91  sup_time_total:                         0.
% 1.01/0.91  sup_time_generating:                    0.
% 1.01/0.91  sup_time_sim_full:                      0.
% 1.01/0.91  sup_time_sim_immed:                     0.
% 1.01/0.91  
% 1.01/0.91  sup_num_of_clauses:                     12
% 1.01/0.91  sup_num_in_active:                      4
% 1.01/0.91  sup_num_in_passive:                     8
% 1.01/0.91  sup_num_of_loops:                       4
% 1.01/0.91  sup_fw_superposition:                   2
% 1.01/0.91  sup_bw_superposition:                   0
% 1.01/0.91  sup_immediate_simplified:               0
% 1.01/0.91  sup_given_eliminated:                   0
% 1.01/0.91  comparisons_done:                       0
% 1.01/0.91  comparisons_avoided:                    0
% 1.01/0.91  
% 1.01/0.91  ------ Simplifications
% 1.01/0.91  
% 1.01/0.91  
% 1.01/0.91  sim_fw_subset_subsumed:                 0
% 1.01/0.91  sim_bw_subset_subsumed:                 0
% 1.01/0.91  sim_fw_subsumed:                        0
% 1.01/0.91  sim_bw_subsumed:                        0
% 1.01/0.91  sim_fw_subsumption_res:                 0
% 1.01/0.91  sim_bw_subsumption_res:                 0
% 1.01/0.91  sim_tautology_del:                      0
% 1.01/0.91  sim_eq_tautology_del:                   0
% 1.01/0.91  sim_eq_res_simp:                        0
% 1.01/0.91  sim_fw_demodulated:                     0
% 1.01/0.91  sim_bw_demodulated:                     0
% 1.01/0.91  sim_light_normalised:                   0
% 1.01/0.91  sim_joinable_taut:                      0
% 1.01/0.91  sim_joinable_simp:                      0
% 1.01/0.91  sim_ac_normalised:                      0
% 1.01/0.91  sim_smt_subsumption:                    0
% 1.01/0.91  
%------------------------------------------------------------------------------
