%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:24 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  181 (1677 expanded)
%              Number of clauses        :  115 ( 377 expanded)
%              Number of leaves         :   15 ( 507 expanded)
%              Depth                    :   25
%              Number of atoms          :  850 (11218 expanded)
%              Number of equality atoms :  138 ( 265 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
          & r3_lattices(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k7_lattices(X0,sK4),k7_lattices(X0,X1))
        & r3_lattices(X0,X1,sK4)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK3))
            & r3_lattices(X0,sK3,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK2,k7_lattices(sK2,X2),k7_lattices(sK2,X1))
              & r3_lattices(sK2,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l3_lattices(sK2)
      & v17_lattices(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3))
    & r3_lattices(sK2,sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v17_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f43,f42,f41])).

fof(f67,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    v17_lattices(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f46,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f18])).

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

fof(f50,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f48,plain,(
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

fof(f40,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f49,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    r3_lattices(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ~ r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_816,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1015,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_817,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1014,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),k7_lattices(X1,X2)) = k7_lattices(X1,k3_lattices(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( v17_lattices(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),k7_lattices(X1,X2)) = k7_lattices(X1,k3_lattices(X1,X0,X2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | k4_lattices(sK2,k7_lattices(sK2,X1),k7_lattices(sK2,X0)) = k7_lattices(sK2,k3_lattices(sK2,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_22,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k4_lattices(sK2,k7_lattices(sK2,X1),k7_lattices(sK2,X0)) = k7_lattices(sK2,k3_lattices(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_25,c_24,c_22])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k4_lattices(sK2,k7_lattices(sK2,X1),k7_lattices(sK2,X0)) = k7_lattices(sK2,k3_lattices(sK2,X1,X0)) ),
    inference(renaming,[status(thm)],[c_315])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
    | k4_lattices(sK2,k7_lattices(sK2,X1_51),k7_lattices(sK2,X0_51)) = k7_lattices(sK2,k3_lattices(sK2,X1_51,X0_51)) ),
    inference(subtyping,[status(esa)],[c_316])).

cnf(c_1016,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,X0_51),k7_lattices(sK2,X1_51)) = k7_lattices(sK2,k3_lattices(sK2,X0_51,X1_51))
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_1318,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,X0_51),k7_lattices(sK2,sK4)) = k7_lattices(sK2,k3_lattices(sK2,X0_51,sK4))
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_1016])).

cnf(c_1467,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4)) = k7_lattices(sK2,k3_lattices(sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1015,c_1318])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_11])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_280])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_24])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k3_lattices(sK2,X1,X0) = k1_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k3_lattices(sK2,X1,X0) = k1_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_25,c_22])).

cnf(c_814,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
    | k3_lattices(sK2,X1_51,X0_51) = k1_lattices(sK2,X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_404])).

cnf(c_1017,plain,
    ( k3_lattices(sK2,X0_51,X1_51) = k1_lattices(sK2,X0_51,X1_51)
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_1164,plain,
    ( k3_lattices(sK2,X0_51,sK4) = k1_lattices(sK2,X0_51,sK4)
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_1017])).

cnf(c_1259,plain,
    ( k3_lattices(sK2,sK3,sK4) = k1_lattices(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1015,c_1164])).

cnf(c_1474,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4)) = k7_lattices(sK2,k1_lattices(sK2,sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_1467,c_1259])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_81,plain,
    ( v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_25,c_24,c_22,c_81])).

cnf(c_812,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X0_51,X1_51),X1_51) = X1_51 ),
    inference(subtyping,[status(esa)],[c_644])).

cnf(c_1019,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,X0_51,X1_51),X1_51) = X1_51
    | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_1565,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,X0_51,sK4),sK4) = sK4
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_1019])).

cnf(c_1689,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_1015,c_1565])).

cnf(c_15,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_388,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_389,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | v9_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_84,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | v9_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_391,plain,
    ( v9_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_25,c_24,c_22,c_84])).

cnf(c_557,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_391])).

cnf(c_558,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k2_lattices(sK2,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_lattices(sK2,X0,X1)
    | k2_lattices(sK2,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_25,c_24,c_22,c_81])).

cnf(c_563,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_562])).

cnf(c_19,negated_conjecture,
    ( r3_lattices(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_366,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_367,plain,
    ( v6_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_78,plain,
    ( v6_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_369,plain,
    ( v6_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_25,c_24,c_22,c_78])).

cnf(c_451,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_369])).

cnf(c_452,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v9_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_456,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_25,c_24,c_22,c_81,c_84])).

cnf(c_457,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_537,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sK3 != X0
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_457])).

cnf(c_538,plain,
    ( r1_lattices(sK2,sK3,sK4)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_540,plain,
    ( r1_lattices(sK2,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_21,c_20])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) = X0
    | sK3 != X0
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_563,c_540])).

cnf(c_718,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | k2_lattices(sK2,sK3,sK4) = sK3 ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_720,plain,
    ( k2_lattices(sK2,sK3,sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_21,c_20])).

cnf(c_808,plain,
    ( k2_lattices(sK2,sK3,sK4) = sK3 ),
    inference(subtyping,[status(esa)],[c_720])).

cnf(c_1696,plain,
    ( k1_lattices(sK2,sK3,sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_1689,c_808])).

cnf(c_2021,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4)) = k7_lattices(sK2,sK4) ),
    inference(light_normalisation,[status(thm)],[c_1474,c_1696])).

cnf(c_16,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_430,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_369])).

cnf(c_431,plain,
    ( r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_25,c_24,c_22,c_81])).

cnf(c_436,plain,
    ( r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_435])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | X3 != X1
    | k4_lattices(sK2,X1,X2) != X0
    | k2_lattices(sK2,X0,X3) = X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_436,c_563])).

cnf(c_669,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k4_lattices(sK2,X1,X0),u1_struct_0(sK2))
    | k2_lattices(sK2,k4_lattices(sK2,X1,X0),X1) = k4_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_811,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
    | ~ m1_subset_1(k4_lattices(sK2,X1_51,X0_51),u1_struct_0(sK2))
    | k2_lattices(sK2,k4_lattices(sK2,X1_51,X0_51),X1_51) = k4_lattices(sK2,X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_669])).

cnf(c_1020,plain,
    ( k2_lattices(sK2,k4_lattices(sK2,X0_51,X1_51),X0_51) = k4_lattices(sK2,X0_51,X1_51)
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k4_lattices(sK2,X0_51,X1_51),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_2023,plain,
    ( k2_lattices(sK2,k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4)),k7_lattices(sK2,sK3)) = k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4))
    | m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2021,c_1020])).

cnf(c_2024,plain,
    ( k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k7_lattices(sK2,sK4)
    | m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2023,c_2021])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2))
    | ~ l3_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_626,plain,
    ( m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_22])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_626])).

cnf(c_813,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
    | m1_subset_1(k7_lattices(sK2,X0_51),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_627])).

cnf(c_1103,plain,
    ( m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_1104,plain,
    ( m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1103])).

cnf(c_14,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_581,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_391])).

cnf(c_582,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k2_lattices(sK2,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_lattices(sK2,X0,X1)
    | k2_lattices(sK2,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_25,c_24,c_22,c_81])).

cnf(c_587,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_586])).

cnf(c_18,negated_conjecture,
    ( ~ r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_475,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_369])).

cnf(c_476,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v9_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_480,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_25,c_24,c_22,c_81,c_84])).

cnf(c_481,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_524,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k7_lattices(sK2,sK3) != X1
    | k7_lattices(sK2,sK4) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_481])).

cnf(c_525,plain,
    ( ~ r1_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3))
    | ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_704,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) != X0
    | k7_lattices(sK2,sK3) != X1
    | k7_lattices(sK2,sK4) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_587,c_525])).

cnf(c_705,plain,
    ( ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
    | k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) != k7_lattices(sK2,sK4) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_809,plain,
    ( ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
    | k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) != k7_lattices(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_705])).

cnf(c_843,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_lattices(sK2,X0_51),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_845,plain,
    ( m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_844,plain,
    ( m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2024,c_1104,c_1103,c_809,c_845,c_844,c_31,c_20,c_30,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:40:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.36/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/0.96  
% 2.36/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/0.96  
% 2.36/0.96  ------  iProver source info
% 2.36/0.96  
% 2.36/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.36/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/0.96  git: non_committed_changes: false
% 2.36/0.96  git: last_make_outside_of_git: false
% 2.36/0.96  
% 2.36/0.96  ------ 
% 2.36/0.96  
% 2.36/0.96  ------ Input Options
% 2.36/0.96  
% 2.36/0.96  --out_options                           all
% 2.36/0.96  --tptp_safe_out                         true
% 2.36/0.96  --problem_path                          ""
% 2.36/0.96  --include_path                          ""
% 2.36/0.96  --clausifier                            res/vclausify_rel
% 2.36/0.96  --clausifier_options                    --mode clausify
% 2.36/0.96  --stdin                                 false
% 2.36/0.96  --stats_out                             all
% 2.36/0.96  
% 2.36/0.96  ------ General Options
% 2.36/0.96  
% 2.36/0.96  --fof                                   false
% 2.36/0.96  --time_out_real                         305.
% 2.36/0.96  --time_out_virtual                      -1.
% 2.36/0.96  --symbol_type_check                     false
% 2.36/0.96  --clausify_out                          false
% 2.36/0.96  --sig_cnt_out                           false
% 2.36/0.96  --trig_cnt_out                          false
% 2.36/0.96  --trig_cnt_out_tolerance                1.
% 2.36/0.96  --trig_cnt_out_sk_spl                   false
% 2.36/0.96  --abstr_cl_out                          false
% 2.36/0.96  
% 2.36/0.96  ------ Global Options
% 2.36/0.96  
% 2.36/0.96  --schedule                              default
% 2.36/0.96  --add_important_lit                     false
% 2.36/0.96  --prop_solver_per_cl                    1000
% 2.36/0.96  --min_unsat_core                        false
% 2.36/0.96  --soft_assumptions                      false
% 2.36/0.96  --soft_lemma_size                       3
% 2.36/0.96  --prop_impl_unit_size                   0
% 2.36/0.96  --prop_impl_unit                        []
% 2.36/0.96  --share_sel_clauses                     true
% 2.36/0.96  --reset_solvers                         false
% 2.36/0.96  --bc_imp_inh                            [conj_cone]
% 2.36/0.96  --conj_cone_tolerance                   3.
% 2.36/0.96  --extra_neg_conj                        none
% 2.36/0.96  --large_theory_mode                     true
% 2.36/0.96  --prolific_symb_bound                   200
% 2.36/0.96  --lt_threshold                          2000
% 2.36/0.96  --clause_weak_htbl                      true
% 2.36/0.96  --gc_record_bc_elim                     false
% 2.36/0.96  
% 2.36/0.96  ------ Preprocessing Options
% 2.36/0.96  
% 2.36/0.96  --preprocessing_flag                    true
% 2.36/0.96  --time_out_prep_mult                    0.1
% 2.36/0.96  --splitting_mode                        input
% 2.36/0.96  --splitting_grd                         true
% 2.36/0.96  --splitting_cvd                         false
% 2.36/0.96  --splitting_cvd_svl                     false
% 2.36/0.96  --splitting_nvd                         32
% 2.36/0.96  --sub_typing                            true
% 2.36/0.96  --prep_gs_sim                           true
% 2.36/0.96  --prep_unflatten                        true
% 2.36/0.96  --prep_res_sim                          true
% 2.36/0.96  --prep_upred                            true
% 2.36/0.96  --prep_sem_filter                       exhaustive
% 2.36/0.96  --prep_sem_filter_out                   false
% 2.36/0.96  --pred_elim                             true
% 2.36/0.96  --res_sim_input                         true
% 2.36/0.96  --eq_ax_congr_red                       true
% 2.36/0.96  --pure_diseq_elim                       true
% 2.36/0.96  --brand_transform                       false
% 2.36/0.96  --non_eq_to_eq                          false
% 2.36/0.96  --prep_def_merge                        true
% 2.36/0.96  --prep_def_merge_prop_impl              false
% 2.36/0.96  --prep_def_merge_mbd                    true
% 2.36/0.96  --prep_def_merge_tr_red                 false
% 2.36/0.96  --prep_def_merge_tr_cl                  false
% 2.36/0.96  --smt_preprocessing                     true
% 2.36/0.96  --smt_ac_axioms                         fast
% 2.36/0.96  --preprocessed_out                      false
% 2.36/0.96  --preprocessed_stats                    false
% 2.36/0.96  
% 2.36/0.96  ------ Abstraction refinement Options
% 2.36/0.96  
% 2.36/0.96  --abstr_ref                             []
% 2.36/0.96  --abstr_ref_prep                        false
% 2.36/0.96  --abstr_ref_until_sat                   false
% 2.36/0.96  --abstr_ref_sig_restrict                funpre
% 2.36/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.96  --abstr_ref_under                       []
% 2.36/0.96  
% 2.36/0.96  ------ SAT Options
% 2.36/0.96  
% 2.36/0.96  --sat_mode                              false
% 2.36/0.96  --sat_fm_restart_options                ""
% 2.36/0.96  --sat_gr_def                            false
% 2.36/0.96  --sat_epr_types                         true
% 2.36/0.96  --sat_non_cyclic_types                  false
% 2.36/0.96  --sat_finite_models                     false
% 2.36/0.96  --sat_fm_lemmas                         false
% 2.36/0.96  --sat_fm_prep                           false
% 2.36/0.96  --sat_fm_uc_incr                        true
% 2.36/0.96  --sat_out_model                         small
% 2.36/0.96  --sat_out_clauses                       false
% 2.36/0.96  
% 2.36/0.96  ------ QBF Options
% 2.36/0.96  
% 2.36/0.96  --qbf_mode                              false
% 2.36/0.96  --qbf_elim_univ                         false
% 2.36/0.96  --qbf_dom_inst                          none
% 2.36/0.96  --qbf_dom_pre_inst                      false
% 2.36/0.96  --qbf_sk_in                             false
% 2.36/0.96  --qbf_pred_elim                         true
% 2.36/0.96  --qbf_split                             512
% 2.36/0.96  
% 2.36/0.96  ------ BMC1 Options
% 2.36/0.96  
% 2.36/0.96  --bmc1_incremental                      false
% 2.36/0.96  --bmc1_axioms                           reachable_all
% 2.36/0.96  --bmc1_min_bound                        0
% 2.36/0.96  --bmc1_max_bound                        -1
% 2.36/0.96  --bmc1_max_bound_default                -1
% 2.36/0.96  --bmc1_symbol_reachability              true
% 2.36/0.96  --bmc1_property_lemmas                  false
% 2.36/0.96  --bmc1_k_induction                      false
% 2.36/0.96  --bmc1_non_equiv_states                 false
% 2.36/0.96  --bmc1_deadlock                         false
% 2.36/0.96  --bmc1_ucm                              false
% 2.36/0.96  --bmc1_add_unsat_core                   none
% 2.36/0.96  --bmc1_unsat_core_children              false
% 2.36/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.96  --bmc1_out_stat                         full
% 2.36/0.96  --bmc1_ground_init                      false
% 2.36/0.96  --bmc1_pre_inst_next_state              false
% 2.36/0.96  --bmc1_pre_inst_state                   false
% 2.36/0.96  --bmc1_pre_inst_reach_state             false
% 2.36/0.96  --bmc1_out_unsat_core                   false
% 2.36/0.96  --bmc1_aig_witness_out                  false
% 2.36/0.96  --bmc1_verbose                          false
% 2.36/0.96  --bmc1_dump_clauses_tptp                false
% 2.36/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.96  --bmc1_dump_file                        -
% 2.36/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.96  --bmc1_ucm_extend_mode                  1
% 2.36/0.96  --bmc1_ucm_init_mode                    2
% 2.36/0.96  --bmc1_ucm_cone_mode                    none
% 2.36/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.96  --bmc1_ucm_relax_model                  4
% 2.36/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.96  --bmc1_ucm_layered_model                none
% 2.36/0.96  --bmc1_ucm_max_lemma_size               10
% 2.36/0.96  
% 2.36/0.96  ------ AIG Options
% 2.36/0.96  
% 2.36/0.96  --aig_mode                              false
% 2.36/0.96  
% 2.36/0.96  ------ Instantiation Options
% 2.36/0.96  
% 2.36/0.96  --instantiation_flag                    true
% 2.36/0.96  --inst_sos_flag                         false
% 2.36/0.96  --inst_sos_phase                        true
% 2.36/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.96  --inst_lit_sel_side                     num_symb
% 2.36/0.96  --inst_solver_per_active                1400
% 2.36/0.96  --inst_solver_calls_frac                1.
% 2.36/0.96  --inst_passive_queue_type               priority_queues
% 2.36/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.96  --inst_passive_queues_freq              [25;2]
% 2.36/0.96  --inst_dismatching                      true
% 2.36/0.96  --inst_eager_unprocessed_to_passive     true
% 2.36/0.96  --inst_prop_sim_given                   true
% 2.36/0.96  --inst_prop_sim_new                     false
% 2.36/0.96  --inst_subs_new                         false
% 2.36/0.96  --inst_eq_res_simp                      false
% 2.36/0.96  --inst_subs_given                       false
% 2.36/0.96  --inst_orphan_elimination               true
% 2.36/0.96  --inst_learning_loop_flag               true
% 2.36/0.96  --inst_learning_start                   3000
% 2.36/0.96  --inst_learning_factor                  2
% 2.36/0.96  --inst_start_prop_sim_after_learn       3
% 2.36/0.96  --inst_sel_renew                        solver
% 2.36/0.96  --inst_lit_activity_flag                true
% 2.36/0.96  --inst_restr_to_given                   false
% 2.36/0.96  --inst_activity_threshold               500
% 2.36/0.96  --inst_out_proof                        true
% 2.36/0.96  
% 2.36/0.96  ------ Resolution Options
% 2.36/0.96  
% 2.36/0.96  --resolution_flag                       true
% 2.36/0.96  --res_lit_sel                           adaptive
% 2.36/0.96  --res_lit_sel_side                      none
% 2.36/0.96  --res_ordering                          kbo
% 2.36/0.96  --res_to_prop_solver                    active
% 2.36/0.96  --res_prop_simpl_new                    false
% 2.36/0.96  --res_prop_simpl_given                  true
% 2.36/0.96  --res_passive_queue_type                priority_queues
% 2.36/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.96  --res_passive_queues_freq               [15;5]
% 2.36/0.96  --res_forward_subs                      full
% 2.36/0.96  --res_backward_subs                     full
% 2.36/0.96  --res_forward_subs_resolution           true
% 2.36/0.96  --res_backward_subs_resolution          true
% 2.36/0.96  --res_orphan_elimination                true
% 2.36/0.96  --res_time_limit                        2.
% 2.36/0.96  --res_out_proof                         true
% 2.36/0.96  
% 2.36/0.96  ------ Superposition Options
% 2.36/0.96  
% 2.36/0.96  --superposition_flag                    true
% 2.36/0.96  --sup_passive_queue_type                priority_queues
% 2.36/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.96  --demod_completeness_check              fast
% 2.36/0.96  --demod_use_ground                      true
% 2.36/0.96  --sup_to_prop_solver                    passive
% 2.36/0.96  --sup_prop_simpl_new                    true
% 2.36/0.96  --sup_prop_simpl_given                  true
% 2.36/0.96  --sup_fun_splitting                     false
% 2.36/0.96  --sup_smt_interval                      50000
% 2.36/0.96  
% 2.36/0.96  ------ Superposition Simplification Setup
% 2.36/0.96  
% 2.36/0.96  --sup_indices_passive                   []
% 2.36/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.96  --sup_full_bw                           [BwDemod]
% 2.36/0.96  --sup_immed_triv                        [TrivRules]
% 2.36/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.96  --sup_immed_bw_main                     []
% 2.36/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.96  
% 2.36/0.96  ------ Combination Options
% 2.36/0.96  
% 2.36/0.96  --comb_res_mult                         3
% 2.36/0.96  --comb_sup_mult                         2
% 2.36/0.96  --comb_inst_mult                        10
% 2.36/0.96  
% 2.36/0.96  ------ Debug Options
% 2.36/0.96  
% 2.36/0.96  --dbg_backtrace                         false
% 2.36/0.96  --dbg_dump_prop_clauses                 false
% 2.36/0.96  --dbg_dump_prop_clauses_file            -
% 2.36/0.96  --dbg_out_stat                          false
% 2.36/0.96  ------ Parsing...
% 2.36/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/0.96  
% 2.36/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.36/0.96  
% 2.36/0.96  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/0.96  
% 2.36/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/0.96  ------ Proving...
% 2.36/0.96  ------ Problem Properties 
% 2.36/0.96  
% 2.36/0.96  
% 2.36/0.96  clauses                                 12
% 2.36/0.96  conjectures                             2
% 2.36/0.96  EPR                                     0
% 2.36/0.96  Horn                                    12
% 2.36/0.96  unary                                   3
% 2.36/0.96  binary                                  2
% 2.36/0.96  lits                                    29
% 2.36/0.96  lits eq                                 9
% 2.36/0.96  fd_pure                                 0
% 2.36/0.96  fd_pseudo                               0
% 2.36/0.96  fd_cond                                 0
% 2.36/0.96  fd_pseudo_cond                          0
% 2.36/0.96  AC symbols                              0
% 2.36/0.96  
% 2.36/0.96  ------ Schedule dynamic 5 is on 
% 2.36/0.96  
% 2.36/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/0.96  
% 2.36/0.96  
% 2.36/0.96  ------ 
% 2.36/0.96  Current options:
% 2.36/0.96  ------ 
% 2.36/0.96  
% 2.36/0.96  ------ Input Options
% 2.36/0.96  
% 2.36/0.96  --out_options                           all
% 2.36/0.96  --tptp_safe_out                         true
% 2.36/0.96  --problem_path                          ""
% 2.36/0.96  --include_path                          ""
% 2.36/0.96  --clausifier                            res/vclausify_rel
% 2.36/0.96  --clausifier_options                    --mode clausify
% 2.36/0.96  --stdin                                 false
% 2.36/0.96  --stats_out                             all
% 2.36/0.96  
% 2.36/0.96  ------ General Options
% 2.36/0.96  
% 2.36/0.96  --fof                                   false
% 2.36/0.96  --time_out_real                         305.
% 2.36/0.96  --time_out_virtual                      -1.
% 2.36/0.96  --symbol_type_check                     false
% 2.36/0.96  --clausify_out                          false
% 2.36/0.96  --sig_cnt_out                           false
% 2.36/0.96  --trig_cnt_out                          false
% 2.36/0.96  --trig_cnt_out_tolerance                1.
% 2.36/0.96  --trig_cnt_out_sk_spl                   false
% 2.36/0.96  --abstr_cl_out                          false
% 2.36/0.96  
% 2.36/0.96  ------ Global Options
% 2.36/0.96  
% 2.36/0.96  --schedule                              default
% 2.36/0.96  --add_important_lit                     false
% 2.36/0.96  --prop_solver_per_cl                    1000
% 2.36/0.96  --min_unsat_core                        false
% 2.36/0.96  --soft_assumptions                      false
% 2.36/0.96  --soft_lemma_size                       3
% 2.36/0.96  --prop_impl_unit_size                   0
% 2.36/0.96  --prop_impl_unit                        []
% 2.36/0.96  --share_sel_clauses                     true
% 2.36/0.96  --reset_solvers                         false
% 2.36/0.96  --bc_imp_inh                            [conj_cone]
% 2.36/0.96  --conj_cone_tolerance                   3.
% 2.36/0.96  --extra_neg_conj                        none
% 2.36/0.96  --large_theory_mode                     true
% 2.36/0.96  --prolific_symb_bound                   200
% 2.36/0.96  --lt_threshold                          2000
% 2.36/0.96  --clause_weak_htbl                      true
% 2.36/0.96  --gc_record_bc_elim                     false
% 2.36/0.96  
% 2.36/0.96  ------ Preprocessing Options
% 2.36/0.96  
% 2.36/0.96  --preprocessing_flag                    true
% 2.36/0.96  --time_out_prep_mult                    0.1
% 2.36/0.96  --splitting_mode                        input
% 2.36/0.96  --splitting_grd                         true
% 2.36/0.96  --splitting_cvd                         false
% 2.36/0.96  --splitting_cvd_svl                     false
% 2.36/0.96  --splitting_nvd                         32
% 2.36/0.96  --sub_typing                            true
% 2.36/0.96  --prep_gs_sim                           true
% 2.36/0.96  --prep_unflatten                        true
% 2.36/0.96  --prep_res_sim                          true
% 2.36/0.96  --prep_upred                            true
% 2.36/0.96  --prep_sem_filter                       exhaustive
% 2.36/0.96  --prep_sem_filter_out                   false
% 2.36/0.96  --pred_elim                             true
% 2.36/0.96  --res_sim_input                         true
% 2.36/0.96  --eq_ax_congr_red                       true
% 2.36/0.96  --pure_diseq_elim                       true
% 2.36/0.96  --brand_transform                       false
% 2.36/0.96  --non_eq_to_eq                          false
% 2.36/0.96  --prep_def_merge                        true
% 2.36/0.96  --prep_def_merge_prop_impl              false
% 2.36/0.96  --prep_def_merge_mbd                    true
% 2.36/0.96  --prep_def_merge_tr_red                 false
% 2.36/0.96  --prep_def_merge_tr_cl                  false
% 2.36/0.96  --smt_preprocessing                     true
% 2.36/0.96  --smt_ac_axioms                         fast
% 2.36/0.96  --preprocessed_out                      false
% 2.36/0.96  --preprocessed_stats                    false
% 2.36/0.96  
% 2.36/0.96  ------ Abstraction refinement Options
% 2.36/0.96  
% 2.36/0.96  --abstr_ref                             []
% 2.36/0.96  --abstr_ref_prep                        false
% 2.36/0.96  --abstr_ref_until_sat                   false
% 2.36/0.96  --abstr_ref_sig_restrict                funpre
% 2.36/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.96  --abstr_ref_under                       []
% 2.36/0.96  
% 2.36/0.96  ------ SAT Options
% 2.36/0.96  
% 2.36/0.96  --sat_mode                              false
% 2.36/0.96  --sat_fm_restart_options                ""
% 2.36/0.96  --sat_gr_def                            false
% 2.36/0.96  --sat_epr_types                         true
% 2.36/0.96  --sat_non_cyclic_types                  false
% 2.36/0.96  --sat_finite_models                     false
% 2.36/0.96  --sat_fm_lemmas                         false
% 2.36/0.96  --sat_fm_prep                           false
% 2.36/0.96  --sat_fm_uc_incr                        true
% 2.36/0.96  --sat_out_model                         small
% 2.36/0.96  --sat_out_clauses                       false
% 2.36/0.96  
% 2.36/0.96  ------ QBF Options
% 2.36/0.96  
% 2.36/0.96  --qbf_mode                              false
% 2.36/0.96  --qbf_elim_univ                         false
% 2.36/0.96  --qbf_dom_inst                          none
% 2.36/0.96  --qbf_dom_pre_inst                      false
% 2.36/0.96  --qbf_sk_in                             false
% 2.36/0.96  --qbf_pred_elim                         true
% 2.36/0.96  --qbf_split                             512
% 2.36/0.96  
% 2.36/0.96  ------ BMC1 Options
% 2.36/0.96  
% 2.36/0.96  --bmc1_incremental                      false
% 2.36/0.96  --bmc1_axioms                           reachable_all
% 2.36/0.96  --bmc1_min_bound                        0
% 2.36/0.96  --bmc1_max_bound                        -1
% 2.36/0.96  --bmc1_max_bound_default                -1
% 2.36/0.96  --bmc1_symbol_reachability              true
% 2.36/0.96  --bmc1_property_lemmas                  false
% 2.36/0.96  --bmc1_k_induction                      false
% 2.36/0.96  --bmc1_non_equiv_states                 false
% 2.36/0.96  --bmc1_deadlock                         false
% 2.36/0.96  --bmc1_ucm                              false
% 2.36/0.96  --bmc1_add_unsat_core                   none
% 2.36/0.96  --bmc1_unsat_core_children              false
% 2.36/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.96  --bmc1_out_stat                         full
% 2.36/0.96  --bmc1_ground_init                      false
% 2.36/0.96  --bmc1_pre_inst_next_state              false
% 2.36/0.96  --bmc1_pre_inst_state                   false
% 2.36/0.96  --bmc1_pre_inst_reach_state             false
% 2.36/0.96  --bmc1_out_unsat_core                   false
% 2.36/0.96  --bmc1_aig_witness_out                  false
% 2.36/0.96  --bmc1_verbose                          false
% 2.36/0.96  --bmc1_dump_clauses_tptp                false
% 2.36/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.96  --bmc1_dump_file                        -
% 2.36/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.96  --bmc1_ucm_extend_mode                  1
% 2.36/0.96  --bmc1_ucm_init_mode                    2
% 2.36/0.96  --bmc1_ucm_cone_mode                    none
% 2.36/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.96  --bmc1_ucm_relax_model                  4
% 2.36/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.96  --bmc1_ucm_layered_model                none
% 2.36/0.96  --bmc1_ucm_max_lemma_size               10
% 2.36/0.96  
% 2.36/0.96  ------ AIG Options
% 2.36/0.96  
% 2.36/0.96  --aig_mode                              false
% 2.36/0.96  
% 2.36/0.96  ------ Instantiation Options
% 2.36/0.96  
% 2.36/0.96  --instantiation_flag                    true
% 2.36/0.96  --inst_sos_flag                         false
% 2.36/0.96  --inst_sos_phase                        true
% 2.36/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.96  --inst_lit_sel_side                     none
% 2.36/0.96  --inst_solver_per_active                1400
% 2.36/0.96  --inst_solver_calls_frac                1.
% 2.36/0.96  --inst_passive_queue_type               priority_queues
% 2.36/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.96  --inst_passive_queues_freq              [25;2]
% 2.36/0.96  --inst_dismatching                      true
% 2.36/0.96  --inst_eager_unprocessed_to_passive     true
% 2.36/0.96  --inst_prop_sim_given                   true
% 2.36/0.96  --inst_prop_sim_new                     false
% 2.36/0.96  --inst_subs_new                         false
% 2.36/0.96  --inst_eq_res_simp                      false
% 2.36/0.96  --inst_subs_given                       false
% 2.36/0.96  --inst_orphan_elimination               true
% 2.36/0.96  --inst_learning_loop_flag               true
% 2.36/0.96  --inst_learning_start                   3000
% 2.36/0.96  --inst_learning_factor                  2
% 2.36/0.96  --inst_start_prop_sim_after_learn       3
% 2.36/0.96  --inst_sel_renew                        solver
% 2.36/0.96  --inst_lit_activity_flag                true
% 2.36/0.96  --inst_restr_to_given                   false
% 2.36/0.96  --inst_activity_threshold               500
% 2.36/0.96  --inst_out_proof                        true
% 2.36/0.96  
% 2.36/0.96  ------ Resolution Options
% 2.36/0.96  
% 2.36/0.96  --resolution_flag                       false
% 2.36/0.96  --res_lit_sel                           adaptive
% 2.36/0.96  --res_lit_sel_side                      none
% 2.36/0.96  --res_ordering                          kbo
% 2.36/0.96  --res_to_prop_solver                    active
% 2.36/0.96  --res_prop_simpl_new                    false
% 2.36/0.96  --res_prop_simpl_given                  true
% 2.36/0.96  --res_passive_queue_type                priority_queues
% 2.36/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.96  --res_passive_queues_freq               [15;5]
% 2.36/0.96  --res_forward_subs                      full
% 2.36/0.96  --res_backward_subs                     full
% 2.36/0.96  --res_forward_subs_resolution           true
% 2.36/0.96  --res_backward_subs_resolution          true
% 2.36/0.96  --res_orphan_elimination                true
% 2.36/0.96  --res_time_limit                        2.
% 2.36/0.96  --res_out_proof                         true
% 2.36/0.96  
% 2.36/0.96  ------ Superposition Options
% 2.36/0.96  
% 2.36/0.96  --superposition_flag                    true
% 2.36/0.96  --sup_passive_queue_type                priority_queues
% 2.36/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.96  --demod_completeness_check              fast
% 2.36/0.96  --demod_use_ground                      true
% 2.36/0.96  --sup_to_prop_solver                    passive
% 2.36/0.96  --sup_prop_simpl_new                    true
% 2.36/0.96  --sup_prop_simpl_given                  true
% 2.36/0.96  --sup_fun_splitting                     false
% 2.36/0.96  --sup_smt_interval                      50000
% 2.36/0.96  
% 2.36/0.96  ------ Superposition Simplification Setup
% 2.36/0.96  
% 2.36/0.96  --sup_indices_passive                   []
% 2.36/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.96  --sup_full_bw                           [BwDemod]
% 2.36/0.96  --sup_immed_triv                        [TrivRules]
% 2.36/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.96  --sup_immed_bw_main                     []
% 2.36/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.96  
% 2.36/0.96  ------ Combination Options
% 2.36/0.96  
% 2.36/0.96  --comb_res_mult                         3
% 2.36/0.96  --comb_sup_mult                         2
% 2.36/0.96  --comb_inst_mult                        10
% 2.36/0.96  
% 2.36/0.96  ------ Debug Options
% 2.36/0.96  
% 2.36/0.96  --dbg_backtrace                         false
% 2.36/0.96  --dbg_dump_prop_clauses                 false
% 2.36/0.96  --dbg_dump_prop_clauses_file            -
% 2.36/0.96  --dbg_out_stat                          false
% 2.36/0.96  
% 2.36/0.96  
% 2.36/0.96  
% 2.36/0.96  
% 2.36/0.96  ------ Proving...
% 2.36/0.96  
% 2.36/0.96  
% 2.36/0.96  % SZS status Theorem for theBenchmark.p
% 2.36/0.96  
% 2.36/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/0.96  
% 2.36/0.96  fof(f10,conjecture,(
% 2.36/0.96    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 2.36/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.96  
% 2.36/0.96  fof(f11,negated_conjecture,(
% 2.36/0.96    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 2.36/0.96    inference(negated_conjecture,[],[f10])).
% 2.36/0.96  
% 2.36/0.96  fof(f32,plain,(
% 2.36/0.96    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.36/0.96    inference(ennf_transformation,[],[f11])).
% 2.36/0.96  
% 2.36/0.96  fof(f33,plain,(
% 2.36/0.96    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.36/0.96    inference(flattening,[],[f32])).
% 2.36/0.96  
% 2.36/0.96  fof(f43,plain,(
% 2.36/0.96    ( ! [X0,X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (~r3_lattices(X0,k7_lattices(X0,sK4),k7_lattices(X0,X1)) & r3_lattices(X0,X1,sK4) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.36/0.96    introduced(choice_axiom,[])).
% 2.36/0.96  
% 2.36/0.96  fof(f42,plain,(
% 2.36/0.96    ( ! [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK3)) & r3_lattices(X0,sK3,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.36/0.96    introduced(choice_axiom,[])).
% 2.36/0.96  
% 2.36/0.96  fof(f41,plain,(
% 2.36/0.96    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK2,k7_lattices(sK2,X2),k7_lattices(sK2,X1)) & r3_lattices(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l3_lattices(sK2) & v17_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2))),
% 2.36/0.96    introduced(choice_axiom,[])).
% 2.36/0.96  
% 2.36/0.96  fof(f44,plain,(
% 2.36/0.96    ((~r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) & r3_lattices(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l3_lattices(sK2) & v17_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2)),
% 2.36/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f43,f42,f41])).
% 2.36/0.96  
% 2.36/0.96  fof(f67,plain,(
% 2.36/0.96    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.36/0.96    inference(cnf_transformation,[],[f44])).
% 2.36/0.96  
% 2.36/0.96  fof(f68,plain,(
% 2.36/0.96    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.36/0.96    inference(cnf_transformation,[],[f44])).
% 2.36/0.96  
% 2.36/0.96  fof(f9,axiom,(
% 2.36/0.96    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 2.36/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.96  
% 2.36/0.96  fof(f30,plain,(
% 2.36/0.96    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.36/0.96    inference(ennf_transformation,[],[f9])).
% 2.36/0.96  
% 2.36/0.96  fof(f31,plain,(
% 2.36/0.96    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.96    inference(flattening,[],[f30])).
% 2.36/0.96  
% 2.36/0.96  fof(f62,plain,(
% 2.36/0.96    ( ! [X2,X0,X1] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.36/0.96    inference(cnf_transformation,[],[f31])).
% 2.36/0.96  
% 2.36/0.96  fof(f65,plain,(
% 2.36/0.96    v17_lattices(sK2)),
% 2.36/0.96    inference(cnf_transformation,[],[f44])).
% 2.36/0.96  
% 2.36/0.96  fof(f63,plain,(
% 2.36/0.96    ~v2_struct_0(sK2)),
% 2.36/0.96    inference(cnf_transformation,[],[f44])).
% 2.36/0.96  
% 2.36/0.96  fof(f64,plain,(
% 2.36/0.96    v10_lattices(sK2)),
% 2.36/0.96    inference(cnf_transformation,[],[f44])).
% 2.36/0.96  
% 2.36/0.96  fof(f66,plain,(
% 2.36/0.96    l3_lattices(sK2)),
% 2.36/0.96    inference(cnf_transformation,[],[f44])).
% 2.36/0.96  
% 2.36/0.96  fof(f1,axiom,(
% 2.36/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.36/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.96  
% 2.36/0.96  fof(f13,plain,(
% 2.36/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.36/0.96    inference(pure_predicate_removal,[],[f1])).
% 2.36/0.96  
% 2.36/0.96  fof(f14,plain,(
% 2.36/0.96    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.36/0.96    inference(pure_predicate_removal,[],[f13])).
% 2.36/0.96  
% 2.36/0.96  fof(f15,plain,(
% 2.36/0.96    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.36/0.96    inference(ennf_transformation,[],[f14])).
% 2.36/0.96  
% 2.36/0.96  fof(f16,plain,(
% 2.36/0.96    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.36/0.96    inference(flattening,[],[f15])).
% 2.36/0.96  
% 2.36/0.96  fof(f46,plain,(
% 2.36/0.96    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.36/0.96    inference(cnf_transformation,[],[f16])).
% 2.36/0.96  
% 2.36/0.96  fof(f4,axiom,(
% 2.36/0.96    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.36/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.96  
% 2.36/0.96  fof(f12,plain,(
% 2.36/0.96    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 2.36/0.96    inference(pure_predicate_removal,[],[f4])).
% 2.36/0.96  
% 2.36/0.96  fof(f21,plain,(
% 2.36/0.96    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 2.36/0.96    inference(ennf_transformation,[],[f12])).
% 2.36/0.96  
% 2.36/0.96  fof(f55,plain,(
% 2.36/0.96    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 2.36/0.96    inference(cnf_transformation,[],[f21])).
% 2.36/0.96  
% 2.36/0.96  fof(f5,axiom,(
% 2.36/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 2.36/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.96  
% 2.36/0.96  fof(f22,plain,(
% 2.36/0.96    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.36/0.96    inference(ennf_transformation,[],[f5])).
% 2.36/0.96  
% 2.36/0.96  fof(f23,plain,(
% 2.36/0.96    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.96    inference(flattening,[],[f22])).
% 2.36/0.96  
% 2.36/0.96  fof(f56,plain,(
% 2.36/0.96    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.36/0.96    inference(cnf_transformation,[],[f23])).
% 2.36/0.96  
% 2.36/0.96  fof(f2,axiom,(
% 2.36/0.96    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 2.36/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.96  
% 2.36/0.96  fof(f17,plain,(
% 2.36/0.96    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.36/0.97    inference(ennf_transformation,[],[f2])).
% 2.36/0.97  
% 2.36/0.97  fof(f18,plain,(
% 2.36/0.97    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(flattening,[],[f17])).
% 2.36/0.97  
% 2.36/0.97  fof(f34,plain,(
% 2.36/0.97    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(nnf_transformation,[],[f18])).
% 2.36/0.97  
% 2.36/0.97  fof(f35,plain,(
% 2.36/0.97    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(rectify,[],[f34])).
% 2.36/0.97  
% 2.36/0.97  fof(f37,plain,(
% 2.36/0.97    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 2.36/0.97    introduced(choice_axiom,[])).
% 2.36/0.97  
% 2.36/0.97  fof(f36,plain,(
% 2.36/0.97    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 2.36/0.97    introduced(choice_axiom,[])).
% 2.36/0.97  
% 2.36/0.97  fof(f38,plain,(
% 2.36/0.97    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 2.36/0.97  
% 2.36/0.97  fof(f50,plain,(
% 2.36/0.97    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f38])).
% 2.36/0.97  
% 2.36/0.97  fof(f48,plain,(
% 2.36/0.97    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f16])).
% 2.36/0.97  
% 2.36/0.97  fof(f7,axiom,(
% 2.36/0.97    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 2.36/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f26,plain,(
% 2.36/0.97    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 2.36/0.97    inference(ennf_transformation,[],[f7])).
% 2.36/0.97  
% 2.36/0.97  fof(f27,plain,(
% 2.36/0.97    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(flattening,[],[f26])).
% 2.36/0.97  
% 2.36/0.97  fof(f40,plain,(
% 2.36/0.97    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(nnf_transformation,[],[f27])).
% 2.36/0.97  
% 2.36/0.97  fof(f59,plain,(
% 2.36/0.97    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f40])).
% 2.36/0.97  
% 2.36/0.97  fof(f49,plain,(
% 2.36/0.97    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f16])).
% 2.36/0.97  
% 2.36/0.97  fof(f69,plain,(
% 2.36/0.97    r3_lattices(sK2,sK3,sK4)),
% 2.36/0.97    inference(cnf_transformation,[],[f44])).
% 2.36/0.97  
% 2.36/0.97  fof(f6,axiom,(
% 2.36/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.36/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f24,plain,(
% 2.36/0.97    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.36/0.97    inference(ennf_transformation,[],[f6])).
% 2.36/0.97  
% 2.36/0.97  fof(f25,plain,(
% 2.36/0.97    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(flattening,[],[f24])).
% 2.36/0.97  
% 2.36/0.97  fof(f39,plain,(
% 2.36/0.97    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(nnf_transformation,[],[f25])).
% 2.36/0.97  
% 2.36/0.97  fof(f57,plain,(
% 2.36/0.97    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f39])).
% 2.36/0.97  
% 2.36/0.97  fof(f47,plain,(
% 2.36/0.97    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f16])).
% 2.36/0.97  
% 2.36/0.97  fof(f8,axiom,(
% 2.36/0.97    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 2.36/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f28,plain,(
% 2.36/0.97    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.36/0.97    inference(ennf_transformation,[],[f8])).
% 2.36/0.97  
% 2.36/0.97  fof(f29,plain,(
% 2.36/0.97    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(flattening,[],[f28])).
% 2.36/0.97  
% 2.36/0.97  fof(f61,plain,(
% 2.36/0.97    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f29])).
% 2.36/0.97  
% 2.36/0.97  fof(f3,axiom,(
% 2.36/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 2.36/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.97  
% 2.36/0.97  fof(f19,plain,(
% 2.36/0.97    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.36/0.97    inference(ennf_transformation,[],[f3])).
% 2.36/0.97  
% 2.36/0.97  fof(f20,plain,(
% 2.36/0.97    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.36/0.97    inference(flattening,[],[f19])).
% 2.36/0.97  
% 2.36/0.97  fof(f54,plain,(
% 2.36/0.97    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f20])).
% 2.36/0.97  
% 2.36/0.97  fof(f60,plain,(
% 2.36/0.97    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f40])).
% 2.36/0.97  
% 2.36/0.97  fof(f70,plain,(
% 2.36/0.97    ~r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3))),
% 2.36/0.97    inference(cnf_transformation,[],[f44])).
% 2.36/0.97  
% 2.36/0.97  fof(f58,plain,(
% 2.36/0.97    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.36/0.97    inference(cnf_transformation,[],[f39])).
% 2.36/0.97  
% 2.36/0.97  cnf(c_21,negated_conjecture,
% 2.36/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_816,negated_conjecture,
% 2.36/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(subtyping,[status(esa)],[c_21]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1015,plain,
% 2.36/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_20,negated_conjecture,
% 2.36/0.97      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_817,negated_conjecture,
% 2.36/0.97      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(subtyping,[status(esa)],[c_20]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1014,plain,
% 2.36/0.97      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_17,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ v17_lattices(X1)
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | v2_struct_0(X1)
% 2.36/0.97      | ~ v10_lattices(X1)
% 2.36/0.97      | k4_lattices(X1,k7_lattices(X1,X0),k7_lattices(X1,X2)) = k7_lattices(X1,k3_lattices(X1,X0,X2)) ),
% 2.36/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_23,negated_conjecture,
% 2.36/0.97      ( v17_lattices(sK2) ),
% 2.36/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_310,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | v2_struct_0(X1)
% 2.36/0.97      | ~ v10_lattices(X1)
% 2.36/0.97      | k4_lattices(X1,k7_lattices(X1,X0),k7_lattices(X1,X2)) = k7_lattices(X1,k3_lattices(X1,X0,X2))
% 2.36/0.97      | sK2 != X1 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_311,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2)
% 2.36/0.97      | ~ v10_lattices(sK2)
% 2.36/0.97      | k4_lattices(sK2,k7_lattices(sK2,X1),k7_lattices(sK2,X0)) = k7_lattices(sK2,k3_lattices(sK2,X1,X0)) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_310]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_25,negated_conjecture,
% 2.36/0.97      ( ~ v2_struct_0(sK2) ),
% 2.36/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_24,negated_conjecture,
% 2.36/0.97      ( v10_lattices(sK2) ),
% 2.36/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_22,negated_conjecture,
% 2.36/0.97      ( l3_lattices(sK2) ),
% 2.36/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_315,plain,
% 2.36/0.97      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | k4_lattices(sK2,k7_lattices(sK2,X1),k7_lattices(sK2,X0)) = k7_lattices(sK2,k3_lattices(sK2,X1,X0)) ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_311,c_25,c_24,c_22]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_316,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | k4_lattices(sK2,k7_lattices(sK2,X1),k7_lattices(sK2,X0)) = k7_lattices(sK2,k3_lattices(sK2,X1,X0)) ),
% 2.36/0.97      inference(renaming,[status(thm)],[c_315]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_815,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
% 2.36/0.97      | k4_lattices(sK2,k7_lattices(sK2,X1_51),k7_lattices(sK2,X0_51)) = k7_lattices(sK2,k3_lattices(sK2,X1_51,X0_51)) ),
% 2.36/0.97      inference(subtyping,[status(esa)],[c_316]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1016,plain,
% 2.36/0.97      ( k4_lattices(sK2,k7_lattices(sK2,X0_51),k7_lattices(sK2,X1_51)) = k7_lattices(sK2,k3_lattices(sK2,X0_51,X1_51))
% 2.36/0.97      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 2.36/0.97      | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1318,plain,
% 2.36/0.97      ( k4_lattices(sK2,k7_lattices(sK2,X0_51),k7_lattices(sK2,sK4)) = k7_lattices(sK2,k3_lattices(sK2,X0_51,sK4))
% 2.36/0.97      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(superposition,[status(thm)],[c_1014,c_1016]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1467,plain,
% 2.36/0.97      ( k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4)) = k7_lattices(sK2,k3_lattices(sK2,sK3,sK4)) ),
% 2.36/0.97      inference(superposition,[status(thm)],[c_1015,c_1318]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_3,plain,
% 2.36/0.97      ( v4_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v10_lattices(X0) ),
% 2.36/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_10,plain,
% 2.36/0.97      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 2.36/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_11,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ l2_lattices(X1)
% 2.36/0.97      | ~ v4_lattices(X1)
% 2.36/0.97      | v2_struct_0(X1)
% 2.36/0.97      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
% 2.36/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_279,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ v4_lattices(X1)
% 2.36/0.97      | ~ l3_lattices(X3)
% 2.36/0.97      | v2_struct_0(X1)
% 2.36/0.97      | X1 != X3
% 2.36/0.97      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_11]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_280,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ v4_lattices(X1)
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | v2_struct_0(X1)
% 2.36/0.97      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_279]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_335,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ l3_lattices(X3)
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | v2_struct_0(X3)
% 2.36/0.97      | v2_struct_0(X1)
% 2.36/0.97      | ~ v10_lattices(X3)
% 2.36/0.97      | X1 != X3
% 2.36/0.97      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_280]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_336,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | v2_struct_0(X1)
% 2.36/0.97      | ~ v10_lattices(X1)
% 2.36/0.97      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_335]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_399,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | v2_struct_0(X1)
% 2.36/0.97      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
% 2.36/0.97      | sK2 != X1 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_336,c_24]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_400,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2)
% 2.36/0.97      | k3_lattices(sK2,X1,X0) = k1_lattices(sK2,X1,X0) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_399]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_404,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | k3_lattices(sK2,X1,X0) = k1_lattices(sK2,X1,X0) ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_400,c_25,c_22]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_814,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
% 2.36/0.97      | k3_lattices(sK2,X1_51,X0_51) = k1_lattices(sK2,X1_51,X0_51) ),
% 2.36/0.97      inference(subtyping,[status(esa)],[c_404]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1017,plain,
% 2.36/0.97      ( k3_lattices(sK2,X0_51,X1_51) = k1_lattices(sK2,X0_51,X1_51)
% 2.36/0.97      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 2.36/0.97      | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_814]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1164,plain,
% 2.36/0.97      ( k3_lattices(sK2,X0_51,sK4) = k1_lattices(sK2,X0_51,sK4)
% 2.36/0.97      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(superposition,[status(thm)],[c_1014,c_1017]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1259,plain,
% 2.36/0.97      ( k3_lattices(sK2,sK3,sK4) = k1_lattices(sK2,sK3,sK4) ),
% 2.36/0.97      inference(superposition,[status(thm)],[c_1015,c_1164]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1474,plain,
% 2.36/0.97      ( k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4)) = k7_lattices(sK2,k1_lattices(sK2,sK3,sK4)) ),
% 2.36/0.97      inference(light_normalisation,[status(thm)],[c_1467,c_1259]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_8,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ v8_lattices(X1)
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | v2_struct_0(X1)
% 2.36/0.97      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 2.36/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_639,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.97      | ~ v8_lattices(X1)
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 2.36/0.97      | sK2 != X1 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_640,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ v8_lattices(sK2)
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_639]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1,plain,
% 2.36/0.97      ( v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v10_lattices(X0) ),
% 2.36/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_81,plain,
% 2.36/0.97      ( v8_lattices(sK2)
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2)
% 2.36/0.97      | ~ v10_lattices(sK2) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_644,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_640,c_25,c_24,c_22,c_81]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_812,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
% 2.36/0.97      | k1_lattices(sK2,k2_lattices(sK2,X0_51,X1_51),X1_51) = X1_51 ),
% 2.36/0.97      inference(subtyping,[status(esa)],[c_644]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1019,plain,
% 2.36/0.97      ( k1_lattices(sK2,k2_lattices(sK2,X0_51,X1_51),X1_51) = X1_51
% 2.36/0.97      | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top
% 2.36/0.97      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1565,plain,
% 2.36/0.97      ( k1_lattices(sK2,k2_lattices(sK2,X0_51,sK4),sK4) = sK4
% 2.36/0.97      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(superposition,[status(thm)],[c_1014,c_1019]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1689,plain,
% 2.36/0.97      ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) = sK4 ),
% 2.36/0.97      inference(superposition,[status(thm)],[c_1015,c_1565]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_15,plain,
% 2.36/0.97      ( ~ r1_lattices(X0,X1,X2)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v9_lattices(X0)
% 2.36/0.97      | k2_lattices(X0,X1,X2) = X1 ),
% 2.36/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_0,plain,
% 2.36/0.97      ( ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v10_lattices(X0)
% 2.36/0.97      | v9_lattices(X0) ),
% 2.36/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_388,plain,
% 2.36/0.97      ( ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | v9_lattices(X0)
% 2.36/0.97      | sK2 != X0 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_389,plain,
% 2.36/0.97      ( ~ l3_lattices(sK2) | v2_struct_0(sK2) | v9_lattices(sK2) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_388]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_84,plain,
% 2.36/0.97      ( ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2)
% 2.36/0.97      | ~ v10_lattices(sK2)
% 2.36/0.97      | v9_lattices(sK2) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_391,plain,
% 2.36/0.97      ( v9_lattices(sK2) ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_389,c_25,c_24,c_22,c_84]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_557,plain,
% 2.36/0.97      ( ~ r1_lattices(X0,X1,X2)
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | k2_lattices(X0,X1,X2) = X1
% 2.36/0.97      | sK2 != X0 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_391]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_558,plain,
% 2.36/0.97      ( ~ r1_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ v8_lattices(sK2)
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2)
% 2.36/0.97      | k2_lattices(sK2,X0,X1) = X0 ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_557]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_562,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ r1_lattices(sK2,X0,X1)
% 2.36/0.97      | k2_lattices(sK2,X0,X1) = X0 ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_558,c_25,c_24,c_22,c_81]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_563,plain,
% 2.36/0.97      ( ~ r1_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | k2_lattices(sK2,X0,X1) = X0 ),
% 2.36/0.97      inference(renaming,[status(thm)],[c_562]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_19,negated_conjecture,
% 2.36/0.97      ( r3_lattices(sK2,sK3,sK4) ),
% 2.36/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_13,plain,
% 2.36/0.97      ( r1_lattices(X0,X1,X2)
% 2.36/0.97      | ~ r3_lattices(X0,X1,X2)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ v6_lattices(X0)
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v9_lattices(X0) ),
% 2.36/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_2,plain,
% 2.36/0.97      ( v6_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v10_lattices(X0) ),
% 2.36/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_366,plain,
% 2.36/0.97      ( v6_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | sK2 != X0 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_367,plain,
% 2.36/0.97      ( v6_lattices(sK2) | ~ l3_lattices(sK2) | v2_struct_0(sK2) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_366]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_78,plain,
% 2.36/0.97      ( v6_lattices(sK2)
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2)
% 2.36/0.97      | ~ v10_lattices(sK2) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_369,plain,
% 2.36/0.97      ( v6_lattices(sK2) ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_367,c_25,c_24,c_22,c_78]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_451,plain,
% 2.36/0.97      ( r1_lattices(X0,X1,X2)
% 2.36/0.97      | ~ r3_lattices(X0,X1,X2)
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v9_lattices(X0)
% 2.36/0.97      | sK2 != X0 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_369]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_452,plain,
% 2.36/0.97      ( r1_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ r3_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ v8_lattices(sK2)
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2)
% 2.36/0.97      | ~ v9_lattices(sK2) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_451]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_456,plain,
% 2.36/0.97      ( r1_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ r3_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_452,c_25,c_24,c_22,c_81,c_84]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_457,plain,
% 2.36/0.97      ( r1_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ r3_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(renaming,[status(thm)],[c_456]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_537,plain,
% 2.36/0.97      ( r1_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | sK3 != X0
% 2.36/0.97      | sK4 != X1
% 2.36/0.97      | sK2 != sK2 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_457]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_538,plain,
% 2.36/0.97      ( r1_lattices(sK2,sK3,sK4)
% 2.36/0.97      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_537]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_540,plain,
% 2.36/0.97      ( r1_lattices(sK2,sK3,sK4) ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_538,c_21,c_20]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_717,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | k2_lattices(sK2,X0,X1) = X0
% 2.36/0.97      | sK3 != X0
% 2.36/0.97      | sK4 != X1
% 2.36/0.97      | sK2 != sK2 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_563,c_540]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_718,plain,
% 2.36/0.97      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.36/0.97      | k2_lattices(sK2,sK3,sK4) = sK3 ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_717]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_720,plain,
% 2.36/0.97      ( k2_lattices(sK2,sK3,sK4) = sK3 ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_718,c_21,c_20]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_808,plain,
% 2.36/0.97      ( k2_lattices(sK2,sK3,sK4) = sK3 ),
% 2.36/0.97      inference(subtyping,[status(esa)],[c_720]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1696,plain,
% 2.36/0.97      ( k1_lattices(sK2,sK3,sK4) = sK4 ),
% 2.36/0.97      inference(light_normalisation,[status(thm)],[c_1689,c_808]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_2021,plain,
% 2.36/0.97      ( k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4)) = k7_lattices(sK2,sK4) ),
% 2.36/0.97      inference(light_normalisation,[status(thm)],[c_1474,c_1696]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_16,plain,
% 2.36/0.97      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ v6_lattices(X0)
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0) ),
% 2.36/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_430,plain,
% 2.36/0.97      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | sK2 != X0 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_369]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_431,plain,
% 2.36/0.97      ( r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ v8_lattices(sK2)
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_430]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_435,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0) ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_431,c_25,c_24,c_22,c_81]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_436,plain,
% 2.36/0.97      ( r1_lattices(sK2,k4_lattices(sK2,X0,X1),X0)
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(renaming,[status(thm)],[c_435]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_668,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.36/0.97      | X3 != X1
% 2.36/0.97      | k4_lattices(sK2,X1,X2) != X0
% 2.36/0.97      | k2_lattices(sK2,X0,X3) = X0
% 2.36/0.97      | sK2 != sK2 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_436,c_563]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_669,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(k4_lattices(sK2,X1,X0),u1_struct_0(sK2))
% 2.36/0.97      | k2_lattices(sK2,k4_lattices(sK2,X1,X0),X1) = k4_lattices(sK2,X1,X0) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_668]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_811,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(k4_lattices(sK2,X1_51,X0_51),u1_struct_0(sK2))
% 2.36/0.97      | k2_lattices(sK2,k4_lattices(sK2,X1_51,X0_51),X1_51) = k4_lattices(sK2,X1_51,X0_51) ),
% 2.36/0.97      inference(subtyping,[status(esa)],[c_669]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1020,plain,
% 2.36/0.97      ( k2_lattices(sK2,k4_lattices(sK2,X0_51,X1_51),X0_51) = k4_lattices(sK2,X0_51,X1_51)
% 2.36/0.97      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 2.36/0.97      | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top
% 2.36/0.97      | m1_subset_1(k4_lattices(sK2,X0_51,X1_51),u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_2023,plain,
% 2.36/0.97      ( k2_lattices(sK2,k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4)),k7_lattices(sK2,sK3)) = k4_lattices(sK2,k7_lattices(sK2,sK3),k7_lattices(sK2,sK4))
% 2.36/0.97      | m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2)) != iProver_top
% 2.36/0.97      | m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(superposition,[status(thm)],[c_2021,c_1020]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_2024,plain,
% 2.36/0.97      ( k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k7_lattices(sK2,sK4)
% 2.36/0.97      | m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2)) != iProver_top
% 2.36/0.97      | m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(light_normalisation,[status(thm)],[c_2023,c_2021]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_9,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | v2_struct_0(X1) ),
% 2.36/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_621,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.97      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 2.36/0.97      | ~ l3_lattices(X1)
% 2.36/0.97      | sK2 != X1 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_622,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2))
% 2.36/0.97      | ~ l3_lattices(sK2) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_621]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_626,plain,
% 2.36/0.97      ( m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_622,c_22]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_627,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2)) ),
% 2.36/0.97      inference(renaming,[status(thm)],[c_626]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_813,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0_51,u1_struct_0(sK2))
% 2.36/0.97      | m1_subset_1(k7_lattices(sK2,X0_51),u1_struct_0(sK2)) ),
% 2.36/0.97      inference(subtyping,[status(esa)],[c_627]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1103,plain,
% 2.36/0.97      ( m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_813]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_1104,plain,
% 2.36/0.97      ( m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) = iProver_top
% 2.36/0.97      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_1103]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_14,plain,
% 2.36/0.97      ( r1_lattices(X0,X1,X2)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v9_lattices(X0)
% 2.36/0.97      | k2_lattices(X0,X1,X2) != X1 ),
% 2.36/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_581,plain,
% 2.36/0.97      ( r1_lattices(X0,X1,X2)
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | k2_lattices(X0,X1,X2) != X1
% 2.36/0.97      | sK2 != X0 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_391]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_582,plain,
% 2.36/0.97      ( r1_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ v8_lattices(sK2)
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2)
% 2.36/0.97      | k2_lattices(sK2,X0,X1) != X0 ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_581]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_586,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | r1_lattices(sK2,X0,X1)
% 2.36/0.97      | k2_lattices(sK2,X0,X1) != X0 ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_582,c_25,c_24,c_22,c_81]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_587,plain,
% 2.36/0.97      ( r1_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | k2_lattices(sK2,X0,X1) != X0 ),
% 2.36/0.97      inference(renaming,[status(thm)],[c_586]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_18,negated_conjecture,
% 2.36/0.97      ( ~ r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) ),
% 2.36/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_12,plain,
% 2.36/0.97      ( ~ r1_lattices(X0,X1,X2)
% 2.36/0.97      | r3_lattices(X0,X1,X2)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ v6_lattices(X0)
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v9_lattices(X0) ),
% 2.36/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_475,plain,
% 2.36/0.97      ( ~ r1_lattices(X0,X1,X2)
% 2.36/0.97      | r3_lattices(X0,X1,X2)
% 2.36/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.97      | ~ v8_lattices(X0)
% 2.36/0.97      | ~ l3_lattices(X0)
% 2.36/0.97      | v2_struct_0(X0)
% 2.36/0.97      | ~ v9_lattices(X0)
% 2.36/0.97      | sK2 != X0 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_369]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_476,plain,
% 2.36/0.97      ( ~ r1_lattices(sK2,X0,X1)
% 2.36/0.97      | r3_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ v8_lattices(sK2)
% 2.36/0.97      | ~ l3_lattices(sK2)
% 2.36/0.97      | v2_struct_0(sK2)
% 2.36/0.97      | ~ v9_lattices(sK2) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_475]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_480,plain,
% 2.36/0.97      ( ~ r1_lattices(sK2,X0,X1)
% 2.36/0.97      | r3_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(global_propositional_subsumption,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_476,c_25,c_24,c_22,c_81,c_84]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_481,plain,
% 2.36/0.97      ( ~ r1_lattices(sK2,X0,X1)
% 2.36/0.97      | r3_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(renaming,[status(thm)],[c_480]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_524,plain,
% 2.36/0.97      ( ~ r1_lattices(sK2,X0,X1)
% 2.36/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | k7_lattices(sK2,sK3) != X1
% 2.36/0.97      | k7_lattices(sK2,sK4) != X0
% 2.36/0.97      | sK2 != sK2 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_481]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_525,plain,
% 2.36/0.97      ( ~ r1_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3))
% 2.36/0.97      | ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_524]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_704,plain,
% 2.36/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
% 2.36/0.97      | k2_lattices(sK2,X0,X1) != X0
% 2.36/0.97      | k7_lattices(sK2,sK3) != X1
% 2.36/0.97      | k7_lattices(sK2,sK4) != X0
% 2.36/0.97      | sK2 != sK2 ),
% 2.36/0.97      inference(resolution_lifted,[status(thm)],[c_587,c_525]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_705,plain,
% 2.36/0.97      ( ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
% 2.36/0.97      | k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) != k7_lattices(sK2,sK4) ),
% 2.36/0.97      inference(unflattening,[status(thm)],[c_704]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_809,plain,
% 2.36/0.97      ( ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
% 2.36/0.97      | k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) != k7_lattices(sK2,sK4) ),
% 2.36/0.97      inference(subtyping,[status(esa)],[c_705]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_843,plain,
% 2.36/0.97      ( m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 2.36/0.97      | m1_subset_1(k7_lattices(sK2,X0_51),u1_struct_0(sK2)) = iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_845,plain,
% 2.36/0.97      ( m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2)) = iProver_top
% 2.36/0.97      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_843]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_844,plain,
% 2.36/0.97      ( m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 2.36/0.97      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.36/0.97      inference(instantiation,[status(thm)],[c_813]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_31,plain,
% 2.36/0.97      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(c_30,plain,
% 2.36/0.97      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.36/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.36/0.97  
% 2.36/0.97  cnf(contradiction,plain,
% 2.36/0.97      ( $false ),
% 2.36/0.97      inference(minisat,
% 2.36/0.97                [status(thm)],
% 2.36/0.97                [c_2024,c_1104,c_1103,c_809,c_845,c_844,c_31,c_20,c_30,
% 2.36/0.97                 c_21]) ).
% 2.36/0.97  
% 2.36/0.97  
% 2.36/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/0.97  
% 2.36/0.97  ------                               Statistics
% 2.36/0.97  
% 2.36/0.97  ------ General
% 2.36/0.97  
% 2.36/0.97  abstr_ref_over_cycles:                  0
% 2.36/0.97  abstr_ref_under_cycles:                 0
% 2.36/0.97  gc_basic_clause_elim:                   0
% 2.36/0.97  forced_gc_time:                         0
% 2.36/0.97  parsing_time:                           0.01
% 2.36/0.97  unif_index_cands_time:                  0.
% 2.36/0.97  unif_index_add_time:                    0.
% 2.36/0.97  orderings_time:                         0.
% 2.36/0.97  out_proof_time:                         0.016
% 2.36/0.97  total_time:                             0.105
% 2.36/0.97  num_of_symbols:                         55
% 2.36/0.97  num_of_terms:                           1901
% 2.36/0.97  
% 2.36/0.97  ------ Preprocessing
% 2.36/0.97  
% 2.36/0.97  num_of_splits:                          1
% 2.36/0.97  num_of_split_atoms:                     1
% 2.36/0.97  num_of_reused_defs:                     0
% 2.36/0.97  num_eq_ax_congr_red:                    28
% 2.36/0.97  num_of_sem_filtered_clauses:            1
% 2.36/0.97  num_of_subtypes:                        3
% 2.36/0.97  monotx_restored_types:                  0
% 2.36/0.97  sat_num_of_epr_types:                   0
% 2.36/0.97  sat_num_of_non_cyclic_types:            0
% 2.36/0.97  sat_guarded_non_collapsed_types:        1
% 2.36/0.97  num_pure_diseq_elim:                    0
% 2.36/0.97  simp_replaced_by:                       0
% 2.36/0.97  res_preprocessed:                       75
% 2.36/0.97  prep_upred:                             0
% 2.36/0.97  prep_unflattend:                        28
% 2.36/0.97  smt_new_axioms:                         0
% 2.36/0.97  pred_elim_cands:                        1
% 2.36/0.97  pred_elim:                              11
% 2.36/0.97  pred_elim_cl:                           14
% 2.36/0.97  pred_elim_cycles:                       13
% 2.36/0.97  merged_defs:                            0
% 2.36/0.97  merged_defs_ncl:                        0
% 2.36/0.97  bin_hyper_res:                          0
% 2.36/0.97  prep_cycles:                            4
% 2.36/0.97  pred_elim_time:                         0.009
% 2.36/0.97  splitting_time:                         0.
% 2.36/0.97  sem_filter_time:                        0.
% 2.36/0.97  monotx_time:                            0.
% 2.36/0.97  subtype_inf_time:                       0.
% 2.36/0.97  
% 2.36/0.97  ------ Problem properties
% 2.36/0.97  
% 2.36/0.97  clauses:                                12
% 2.36/0.97  conjectures:                            2
% 2.36/0.97  epr:                                    0
% 2.36/0.97  horn:                                   12
% 2.36/0.97  ground:                                 6
% 2.36/0.97  unary:                                  3
% 2.36/0.97  binary:                                 2
% 2.36/0.97  lits:                                   29
% 2.36/0.97  lits_eq:                                9
% 2.36/0.97  fd_pure:                                0
% 2.36/0.97  fd_pseudo:                              0
% 2.36/0.97  fd_cond:                                0
% 2.36/0.97  fd_pseudo_cond:                         0
% 2.36/0.97  ac_symbols:                             0
% 2.36/0.97  
% 2.36/0.97  ------ Propositional Solver
% 2.36/0.97  
% 2.36/0.97  prop_solver_calls:                      29
% 2.36/0.97  prop_fast_solver_calls:                 619
% 2.36/0.97  smt_solver_calls:                       0
% 2.36/0.97  smt_fast_solver_calls:                  0
% 2.36/0.97  prop_num_of_clauses:                    687
% 2.36/0.97  prop_preprocess_simplified:             2435
% 2.36/0.97  prop_fo_subsumed:                       37
% 2.36/0.97  prop_solver_time:                       0.
% 2.36/0.97  smt_solver_time:                        0.
% 2.36/0.97  smt_fast_solver_time:                   0.
% 2.36/0.97  prop_fast_solver_time:                  0.
% 2.36/0.97  prop_unsat_core_time:                   0.
% 2.36/0.97  
% 2.36/0.97  ------ QBF
% 2.36/0.97  
% 2.36/0.97  qbf_q_res:                              0
% 2.36/0.97  qbf_num_tautologies:                    0
% 2.36/0.97  qbf_prep_cycles:                        0
% 2.36/0.97  
% 2.36/0.97  ------ BMC1
% 2.36/0.97  
% 2.36/0.97  bmc1_current_bound:                     -1
% 2.36/0.97  bmc1_last_solved_bound:                 -1
% 2.36/0.97  bmc1_unsat_core_size:                   -1
% 2.36/0.97  bmc1_unsat_core_parents_size:           -1
% 2.36/0.97  bmc1_merge_next_fun:                    0
% 2.36/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.36/0.97  
% 2.36/0.97  ------ Instantiation
% 2.36/0.97  
% 2.36/0.97  inst_num_of_clauses:                    186
% 2.36/0.97  inst_num_in_passive:                    48
% 2.36/0.97  inst_num_in_active:                     119
% 2.36/0.97  inst_num_in_unprocessed:                19
% 2.36/0.97  inst_num_of_loops:                      130
% 2.36/0.97  inst_num_of_learning_restarts:          0
% 2.36/0.97  inst_num_moves_active_passive:          6
% 2.36/0.97  inst_lit_activity:                      0
% 2.36/0.97  inst_lit_activity_moves:                0
% 2.36/0.97  inst_num_tautologies:                   0
% 2.36/0.97  inst_num_prop_implied:                  0
% 2.36/0.97  inst_num_existing_simplified:           0
% 2.36/0.97  inst_num_eq_res_simplified:             0
% 2.36/0.97  inst_num_child_elim:                    0
% 2.36/0.97  inst_num_of_dismatching_blockings:      47
% 2.36/0.97  inst_num_of_non_proper_insts:           213
% 2.36/0.97  inst_num_of_duplicates:                 0
% 2.36/0.97  inst_inst_num_from_inst_to_res:         0
% 2.36/0.97  inst_dismatching_checking_time:         0.
% 2.36/0.97  
% 2.36/0.97  ------ Resolution
% 2.36/0.97  
% 2.36/0.97  res_num_of_clauses:                     0
% 2.36/0.97  res_num_in_passive:                     0
% 2.36/0.97  res_num_in_active:                      0
% 2.36/0.97  res_num_of_loops:                       79
% 2.36/0.97  res_forward_subset_subsumed:            20
% 2.36/0.97  res_backward_subset_subsumed:           2
% 2.36/0.97  res_forward_subsumed:                   0
% 2.36/0.97  res_backward_subsumed:                  0
% 2.36/0.97  res_forward_subsumption_resolution:     0
% 2.36/0.97  res_backward_subsumption_resolution:    0
% 2.36/0.97  res_clause_to_clause_subsumption:       76
% 2.36/0.97  res_orphan_elimination:                 0
% 2.36/0.97  res_tautology_del:                      50
% 2.36/0.97  res_num_eq_res_simplified:              1
% 2.36/0.97  res_num_sel_changes:                    0
% 2.36/0.97  res_moves_from_active_to_pass:          0
% 2.36/0.97  
% 2.36/0.97  ------ Superposition
% 2.36/0.97  
% 2.36/0.97  sup_time_total:                         0.
% 2.36/0.97  sup_time_generating:                    0.
% 2.36/0.97  sup_time_sim_full:                      0.
% 2.36/0.97  sup_time_sim_immed:                     0.
% 2.36/0.97  
% 2.36/0.97  sup_num_of_clauses:                     40
% 2.36/0.97  sup_num_in_active:                      24
% 2.36/0.97  sup_num_in_passive:                     16
% 2.36/0.97  sup_num_of_loops:                       24
% 2.36/0.97  sup_fw_superposition:                   27
% 2.36/0.97  sup_bw_superposition:                   1
% 2.36/0.97  sup_immediate_simplified:               6
% 2.36/0.97  sup_given_eliminated:                   0
% 2.36/0.97  comparisons_done:                       0
% 2.36/0.97  comparisons_avoided:                    0
% 2.36/0.97  
% 2.36/0.97  ------ Simplifications
% 2.36/0.97  
% 2.36/0.97  
% 2.36/0.97  sim_fw_subset_subsumed:                 0
% 2.36/0.97  sim_bw_subset_subsumed:                 0
% 2.36/0.97  sim_fw_subsumed:                        0
% 2.36/0.97  sim_bw_subsumed:                        0
% 2.36/0.97  sim_fw_subsumption_res:                 0
% 2.36/0.97  sim_bw_subsumption_res:                 0
% 2.36/0.97  sim_tautology_del:                      0
% 2.36/0.97  sim_eq_tautology_del:                   0
% 2.36/0.97  sim_eq_res_simp:                        0
% 2.36/0.97  sim_fw_demodulated:                     0
% 2.36/0.97  sim_bw_demodulated:                     1
% 2.36/0.97  sim_light_normalised:                   7
% 2.36/0.97  sim_joinable_taut:                      0
% 2.36/0.97  sim_joinable_simp:                      0
% 2.36/0.97  sim_ac_normalised:                      0
% 2.36/0.97  sim_smt_subsumption:                    0
% 2.36/0.97  
%------------------------------------------------------------------------------
