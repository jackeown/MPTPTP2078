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
% DateTime   : Thu Dec  3 12:20:08 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  195 (1929 expanded)
%              Number of clauses        :  125 ( 561 expanded)
%              Number of leaves         :   17 ( 505 expanded)
%              Depth                    :   25
%              Number of atoms          :  682 (6346 expanded)
%              Number of equality atoms :  176 ( 782 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK2),k3_xboole_0(X1,sK2))
        & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),sK1,X2),k3_xboole_0(sK1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
        & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v2_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f40,f39,f38])).

fof(f60,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(definition_unfolding,[],[f60,f51])).

fof(f61,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(definition_unfolding,[],[f61,f51])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(definition_unfolding,[],[f59,f51])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f55,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0] : v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f55,f51])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f52,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( v4_orders_2(X0)
                   => k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3)
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3)
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3)
      | ~ v4_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X0] : v4_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X0] : v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k12_lattice3(X0,X1,X2) = X1
                  | ~ r3_orders_2(X0,X1,X2) )
                & ( r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) != X1 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = X1
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0] : v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | k12_lattice3(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f56,f51,f51,f51])).

fof(f58,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f62,f51])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_939,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1249,plain,
    ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_940,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1248,plain,
    ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_943,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_49))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_49))
    | m1_subset_1(k11_lattice3(X0_49,X1_47,X0_47),u1_struct_0(X0_49))
    | ~ l1_orders_2(X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1245,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(k11_lattice3(X0_49,X0_47,X1_47),u1_struct_0(X0_49)) = iProver_top
    | l1_orders_2(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_676,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_677,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_10,plain,
    ( v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_38,plain,
    ( v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_41,plain,
    ( l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_681,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_38,c_41])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) ),
    inference(renaming,[status(thm)],[c_681])).

cnf(c_936,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_682])).

cnf(c_1252,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47)
    | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_1684,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_1252])).

cnf(c_40,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_42,plain,
    ( l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_3591,plain,
    ( m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1684,c_42])).

cnf(c_3592,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3591])).

cnf(c_3601,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47),X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47),X1_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_3592])).

cnf(c_3797,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1),X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1),X0_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_3601])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0)
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_656,c_38,c_41])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) ),
    inference(renaming,[status(thm)],[c_660])).

cnf(c_937,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_661])).

cnf(c_1251,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_1406,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_1251])).

cnf(c_1476,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1249,c_1406])).

cnf(c_3811,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3797,c_1476])).

cnf(c_4122,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1249,c_3811])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3) = k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) = k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3)
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_632,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_11,plain,
    ( v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,plain,
    ( v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_636,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_35,c_38,c_41])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X0),X1) ),
    inference(renaming,[status(thm)],[c_636])).

cnf(c_938,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2_47,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2_47,X0_47),X1_47) ),
    inference(subtyping,[status(esa)],[c_637])).

cnf(c_1250,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X2_47)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47)
    | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_2032,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0_47),X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47))
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1250])).

cnf(c_2367,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_2032])).

cnf(c_2399,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1249,c_2367])).

cnf(c_2410,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(light_normalisation,[status(thm)],[c_2399,c_1476])).

cnf(c_7,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_607,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) = X1
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_608,plain,
    ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_12,plain,
    ( v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,plain,
    ( v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_32,c_38,c_41])).

cnf(c_613,plain,
    ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_612])).

cnf(c_1,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_227,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_566,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_18])).

cnf(c_567,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_571,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_32,c_41])).

cnf(c_572,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(renaming,[status(thm)],[c_571])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | X1 != X0
    | X1 != X2
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X0) = X2
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != g1_orders_2(sK0,k1_yellow_1(sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_613,c_572])).

cnf(c_779,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_778])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_779])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_933])).

cnf(c_1256,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_947,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_933])).

cnf(c_988,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_989,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_945,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_933])).

cnf(c_992,plain,
    ( m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_994,plain,
    ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_2927,plain,
    ( m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1256,c_22,c_988,c_989,c_994])).

cnf(c_2928,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2927])).

cnf(c_2934,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1249,c_2928])).

cnf(c_1559,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1252])).

cnf(c_1939,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1249,c_1559])).

cnf(c_3137,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_2934,c_1939])).

cnf(c_2368,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0_47)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1),X0_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_2032])).

cnf(c_2552,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_1248,c_2368])).

cnf(c_3319,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3137,c_2552])).

cnf(c_3878,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_2410,c_3319])).

cnf(c_4133,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4122,c_3878])).

cnf(c_952,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_2358,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != X0_47
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) != X0_47
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_3423,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_2933,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1248,c_2928])).

cnf(c_1558,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_1252])).

cnf(c_1812,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1248,c_1558])).

cnf(c_3061,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_2933,c_1812])).

cnf(c_2398,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1248,c_2367])).

cnf(c_3236,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3061,c_2398])).

cnf(c_8,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_587,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) != X1
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_588,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_588,c_32,c_38,c_41])).

cnf(c_591,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_590])).

cnf(c_14,plain,
    ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_290,plain,
    ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | r1_tarski(X1,X2)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_291,plain,
    ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(X0,X1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
    inference(resolution,[status(thm)],[c_591,c_291])).

cnf(c_935,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(X0_47,X1_47)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47) != X0_47 ),
    inference(subtyping,[status(esa)],[c_743])).

cnf(c_2655,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_2657,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2655])).

cnf(c_2329,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_1856,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != X0_47
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) != X0_47 ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_2328,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_1489,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != X0_47
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) != X0_47 ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_1669,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_1395,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(X0_50,k1_yellow_1(X0_50))))
    | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(X0_50,k1_yellow_1(X0_50))))
    | m1_subset_1(k11_lattice3(g1_orders_2(X0_50,k1_yellow_1(X0_50)),X0_47,X1_47),u1_struct_0(g1_orders_2(X0_50,k1_yellow_1(X0_50))))
    | ~ l1_orders_2(g1_orders_2(X0_50,k1_yellow_1(X0_50))) ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_1469,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1395])).

cnf(c_1420,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1417,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)
    | m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_944,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | ~ r1_tarski(X0_47,X2_47)
    | r1_tarski(X0_47,k3_xboole_0(X2_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1387,plain,
    ( r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4133,c_3423,c_3236,c_2657,c_2329,c_2328,c_1669,c_1476,c_1469,c_1420,c_1417,c_1387,c_41,c_15,c_16,c_22,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:35:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.98/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/0.99  
% 2.98/0.99  ------  iProver source info
% 2.98/0.99  
% 2.98/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.98/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/0.99  git: non_committed_changes: false
% 2.98/0.99  git: last_make_outside_of_git: false
% 2.98/0.99  
% 2.98/0.99  ------ 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options
% 2.98/0.99  
% 2.98/0.99  --out_options                           all
% 2.98/0.99  --tptp_safe_out                         true
% 2.98/0.99  --problem_path                          ""
% 2.98/0.99  --include_path                          ""
% 2.98/0.99  --clausifier                            res/vclausify_rel
% 2.98/0.99  --clausifier_options                    --mode clausify
% 2.98/0.99  --stdin                                 false
% 2.98/0.99  --stats_out                             all
% 2.98/0.99  
% 2.98/0.99  ------ General Options
% 2.98/0.99  
% 2.98/0.99  --fof                                   false
% 2.98/0.99  --time_out_real                         305.
% 2.98/0.99  --time_out_virtual                      -1.
% 2.98/0.99  --symbol_type_check                     false
% 2.98/0.99  --clausify_out                          false
% 2.98/0.99  --sig_cnt_out                           false
% 2.98/0.99  --trig_cnt_out                          false
% 2.98/0.99  --trig_cnt_out_tolerance                1.
% 2.98/0.99  --trig_cnt_out_sk_spl                   false
% 2.98/0.99  --abstr_cl_out                          false
% 2.98/0.99  
% 2.98/0.99  ------ Global Options
% 2.98/0.99  
% 2.98/0.99  --schedule                              default
% 2.98/0.99  --add_important_lit                     false
% 2.98/0.99  --prop_solver_per_cl                    1000
% 2.98/0.99  --min_unsat_core                        false
% 2.98/0.99  --soft_assumptions                      false
% 2.98/0.99  --soft_lemma_size                       3
% 2.98/0.99  --prop_impl_unit_size                   0
% 2.98/0.99  --prop_impl_unit                        []
% 2.98/0.99  --share_sel_clauses                     true
% 2.98/0.99  --reset_solvers                         false
% 2.98/0.99  --bc_imp_inh                            [conj_cone]
% 2.98/0.99  --conj_cone_tolerance                   3.
% 2.98/0.99  --extra_neg_conj                        none
% 2.98/0.99  --large_theory_mode                     true
% 2.98/0.99  --prolific_symb_bound                   200
% 2.98/0.99  --lt_threshold                          2000
% 2.98/0.99  --clause_weak_htbl                      true
% 2.98/0.99  --gc_record_bc_elim                     false
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing Options
% 2.98/0.99  
% 2.98/0.99  --preprocessing_flag                    true
% 2.98/0.99  --time_out_prep_mult                    0.1
% 2.98/0.99  --splitting_mode                        input
% 2.98/0.99  --splitting_grd                         true
% 2.98/0.99  --splitting_cvd                         false
% 2.98/0.99  --splitting_cvd_svl                     false
% 2.98/0.99  --splitting_nvd                         32
% 2.98/0.99  --sub_typing                            true
% 2.98/0.99  --prep_gs_sim                           true
% 2.98/0.99  --prep_unflatten                        true
% 2.98/0.99  --prep_res_sim                          true
% 2.98/0.99  --prep_upred                            true
% 2.98/0.99  --prep_sem_filter                       exhaustive
% 2.98/0.99  --prep_sem_filter_out                   false
% 2.98/0.99  --pred_elim                             true
% 2.98/0.99  --res_sim_input                         true
% 2.98/0.99  --eq_ax_congr_red                       true
% 2.98/0.99  --pure_diseq_elim                       true
% 2.98/0.99  --brand_transform                       false
% 2.98/0.99  --non_eq_to_eq                          false
% 2.98/0.99  --prep_def_merge                        true
% 2.98/0.99  --prep_def_merge_prop_impl              false
% 2.98/0.99  --prep_def_merge_mbd                    true
% 2.98/0.99  --prep_def_merge_tr_red                 false
% 2.98/0.99  --prep_def_merge_tr_cl                  false
% 2.98/0.99  --smt_preprocessing                     true
% 2.98/0.99  --smt_ac_axioms                         fast
% 2.98/0.99  --preprocessed_out                      false
% 2.98/0.99  --preprocessed_stats                    false
% 2.98/0.99  
% 2.98/0.99  ------ Abstraction refinement Options
% 2.98/0.99  
% 2.98/0.99  --abstr_ref                             []
% 2.98/0.99  --abstr_ref_prep                        false
% 2.98/0.99  --abstr_ref_until_sat                   false
% 2.98/0.99  --abstr_ref_sig_restrict                funpre
% 2.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.99  --abstr_ref_under                       []
% 2.98/0.99  
% 2.98/0.99  ------ SAT Options
% 2.98/0.99  
% 2.98/0.99  --sat_mode                              false
% 2.98/0.99  --sat_fm_restart_options                ""
% 2.98/0.99  --sat_gr_def                            false
% 2.98/0.99  --sat_epr_types                         true
% 2.98/0.99  --sat_non_cyclic_types                  false
% 2.98/0.99  --sat_finite_models                     false
% 2.98/0.99  --sat_fm_lemmas                         false
% 2.98/0.99  --sat_fm_prep                           false
% 2.98/0.99  --sat_fm_uc_incr                        true
% 2.98/0.99  --sat_out_model                         small
% 2.98/0.99  --sat_out_clauses                       false
% 2.98/0.99  
% 2.98/0.99  ------ QBF Options
% 2.98/0.99  
% 2.98/0.99  --qbf_mode                              false
% 2.98/0.99  --qbf_elim_univ                         false
% 2.98/0.99  --qbf_dom_inst                          none
% 2.98/0.99  --qbf_dom_pre_inst                      false
% 2.98/0.99  --qbf_sk_in                             false
% 2.98/0.99  --qbf_pred_elim                         true
% 2.98/0.99  --qbf_split                             512
% 2.98/0.99  
% 2.98/0.99  ------ BMC1 Options
% 2.98/0.99  
% 2.98/0.99  --bmc1_incremental                      false
% 2.98/0.99  --bmc1_axioms                           reachable_all
% 2.98/0.99  --bmc1_min_bound                        0
% 2.98/0.99  --bmc1_max_bound                        -1
% 2.98/0.99  --bmc1_max_bound_default                -1
% 2.98/0.99  --bmc1_symbol_reachability              true
% 2.98/0.99  --bmc1_property_lemmas                  false
% 2.98/0.99  --bmc1_k_induction                      false
% 2.98/0.99  --bmc1_non_equiv_states                 false
% 2.98/0.99  --bmc1_deadlock                         false
% 2.98/0.99  --bmc1_ucm                              false
% 2.98/0.99  --bmc1_add_unsat_core                   none
% 2.98/0.99  --bmc1_unsat_core_children              false
% 2.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.99  --bmc1_out_stat                         full
% 2.98/0.99  --bmc1_ground_init                      false
% 2.98/0.99  --bmc1_pre_inst_next_state              false
% 2.98/0.99  --bmc1_pre_inst_state                   false
% 2.98/0.99  --bmc1_pre_inst_reach_state             false
% 2.98/0.99  --bmc1_out_unsat_core                   false
% 2.98/0.99  --bmc1_aig_witness_out                  false
% 2.98/0.99  --bmc1_verbose                          false
% 2.98/0.99  --bmc1_dump_clauses_tptp                false
% 2.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.99  --bmc1_dump_file                        -
% 2.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.99  --bmc1_ucm_extend_mode                  1
% 2.98/0.99  --bmc1_ucm_init_mode                    2
% 2.98/0.99  --bmc1_ucm_cone_mode                    none
% 2.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.99  --bmc1_ucm_relax_model                  4
% 2.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.99  --bmc1_ucm_layered_model                none
% 2.98/0.99  --bmc1_ucm_max_lemma_size               10
% 2.98/0.99  
% 2.98/0.99  ------ AIG Options
% 2.98/0.99  
% 2.98/0.99  --aig_mode                              false
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation Options
% 2.98/0.99  
% 2.98/0.99  --instantiation_flag                    true
% 2.98/0.99  --inst_sos_flag                         false
% 2.98/0.99  --inst_sos_phase                        true
% 2.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel_side                     num_symb
% 2.98/0.99  --inst_solver_per_active                1400
% 2.98/0.99  --inst_solver_calls_frac                1.
% 2.98/0.99  --inst_passive_queue_type               priority_queues
% 2.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.99  --inst_passive_queues_freq              [25;2]
% 2.98/0.99  --inst_dismatching                      true
% 2.98/0.99  --inst_eager_unprocessed_to_passive     true
% 2.98/0.99  --inst_prop_sim_given                   true
% 2.98/0.99  --inst_prop_sim_new                     false
% 2.98/0.99  --inst_subs_new                         false
% 2.98/0.99  --inst_eq_res_simp                      false
% 2.98/0.99  --inst_subs_given                       false
% 2.98/0.99  --inst_orphan_elimination               true
% 2.98/0.99  --inst_learning_loop_flag               true
% 2.98/0.99  --inst_learning_start                   3000
% 2.98/0.99  --inst_learning_factor                  2
% 2.98/0.99  --inst_start_prop_sim_after_learn       3
% 2.98/0.99  --inst_sel_renew                        solver
% 2.98/0.99  --inst_lit_activity_flag                true
% 2.98/0.99  --inst_restr_to_given                   false
% 2.98/0.99  --inst_activity_threshold               500
% 2.98/0.99  --inst_out_proof                        true
% 2.98/0.99  
% 2.98/0.99  ------ Resolution Options
% 2.98/0.99  
% 2.98/0.99  --resolution_flag                       true
% 2.98/0.99  --res_lit_sel                           adaptive
% 2.98/0.99  --res_lit_sel_side                      none
% 2.98/0.99  --res_ordering                          kbo
% 2.98/0.99  --res_to_prop_solver                    active
% 2.98/0.99  --res_prop_simpl_new                    false
% 2.98/0.99  --res_prop_simpl_given                  true
% 2.98/0.99  --res_passive_queue_type                priority_queues
% 2.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.99  --res_passive_queues_freq               [15;5]
% 2.98/0.99  --res_forward_subs                      full
% 2.98/0.99  --res_backward_subs                     full
% 2.98/0.99  --res_forward_subs_resolution           true
% 2.98/0.99  --res_backward_subs_resolution          true
% 2.98/0.99  --res_orphan_elimination                true
% 2.98/0.99  --res_time_limit                        2.
% 2.98/0.99  --res_out_proof                         true
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Options
% 2.98/0.99  
% 2.98/0.99  --superposition_flag                    true
% 2.98/0.99  --sup_passive_queue_type                priority_queues
% 2.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.99  --demod_completeness_check              fast
% 2.98/0.99  --demod_use_ground                      true
% 2.98/0.99  --sup_to_prop_solver                    passive
% 2.98/0.99  --sup_prop_simpl_new                    true
% 2.98/0.99  --sup_prop_simpl_given                  true
% 2.98/0.99  --sup_fun_splitting                     false
% 2.98/0.99  --sup_smt_interval                      50000
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Simplification Setup
% 2.98/0.99  
% 2.98/0.99  --sup_indices_passive                   []
% 2.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_full_bw                           [BwDemod]
% 2.98/0.99  --sup_immed_triv                        [TrivRules]
% 2.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_immed_bw_main                     []
% 2.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  
% 2.98/0.99  ------ Combination Options
% 2.98/0.99  
% 2.98/0.99  --comb_res_mult                         3
% 2.98/0.99  --comb_sup_mult                         2
% 2.98/0.99  --comb_inst_mult                        10
% 2.98/0.99  
% 2.98/0.99  ------ Debug Options
% 2.98/0.99  
% 2.98/0.99  --dbg_backtrace                         false
% 2.98/0.99  --dbg_dump_prop_clauses                 false
% 2.98/0.99  --dbg_dump_prop_clauses_file            -
% 2.98/0.99  --dbg_out_stat                          false
% 2.98/0.99  ------ Parsing...
% 2.98/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/0.99  ------ Proving...
% 2.98/0.99  ------ Problem Properties 
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  clauses                                 17
% 2.98/0.99  conjectures                             3
% 2.98/0.99  EPR                                     2
% 2.98/0.99  Horn                                    15
% 2.98/0.99  unary                                   4
% 2.98/0.99  binary                                  4
% 2.98/0.99  lits                                    43
% 2.98/0.99  lits eq                                 6
% 2.98/0.99  fd_pure                                 0
% 2.98/0.99  fd_pseudo                               0
% 2.98/0.99  fd_cond                                 0
% 2.98/0.99  fd_pseudo_cond                          0
% 2.98/0.99  AC symbols                              0
% 2.98/0.99  
% 2.98/0.99  ------ Schedule dynamic 5 is on 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  ------ 
% 2.98/0.99  Current options:
% 2.98/0.99  ------ 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options
% 2.98/0.99  
% 2.98/0.99  --out_options                           all
% 2.98/0.99  --tptp_safe_out                         true
% 2.98/0.99  --problem_path                          ""
% 2.98/0.99  --include_path                          ""
% 2.98/0.99  --clausifier                            res/vclausify_rel
% 2.98/0.99  --clausifier_options                    --mode clausify
% 2.98/0.99  --stdin                                 false
% 2.98/0.99  --stats_out                             all
% 2.98/0.99  
% 2.98/0.99  ------ General Options
% 2.98/0.99  
% 2.98/0.99  --fof                                   false
% 2.98/0.99  --time_out_real                         305.
% 2.98/0.99  --time_out_virtual                      -1.
% 2.98/0.99  --symbol_type_check                     false
% 2.98/0.99  --clausify_out                          false
% 2.98/0.99  --sig_cnt_out                           false
% 2.98/0.99  --trig_cnt_out                          false
% 2.98/0.99  --trig_cnt_out_tolerance                1.
% 2.98/0.99  --trig_cnt_out_sk_spl                   false
% 2.98/0.99  --abstr_cl_out                          false
% 2.98/0.99  
% 2.98/0.99  ------ Global Options
% 2.98/0.99  
% 2.98/0.99  --schedule                              default
% 2.98/0.99  --add_important_lit                     false
% 2.98/0.99  --prop_solver_per_cl                    1000
% 2.98/0.99  --min_unsat_core                        false
% 2.98/0.99  --soft_assumptions                      false
% 2.98/0.99  --soft_lemma_size                       3
% 2.98/0.99  --prop_impl_unit_size                   0
% 2.98/0.99  --prop_impl_unit                        []
% 2.98/0.99  --share_sel_clauses                     true
% 2.98/0.99  --reset_solvers                         false
% 2.98/0.99  --bc_imp_inh                            [conj_cone]
% 2.98/0.99  --conj_cone_tolerance                   3.
% 2.98/0.99  --extra_neg_conj                        none
% 2.98/0.99  --large_theory_mode                     true
% 2.98/0.99  --prolific_symb_bound                   200
% 2.98/0.99  --lt_threshold                          2000
% 2.98/0.99  --clause_weak_htbl                      true
% 2.98/0.99  --gc_record_bc_elim                     false
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing Options
% 2.98/0.99  
% 2.98/0.99  --preprocessing_flag                    true
% 2.98/0.99  --time_out_prep_mult                    0.1
% 2.98/0.99  --splitting_mode                        input
% 2.98/0.99  --splitting_grd                         true
% 2.98/0.99  --splitting_cvd                         false
% 2.98/0.99  --splitting_cvd_svl                     false
% 2.98/0.99  --splitting_nvd                         32
% 2.98/0.99  --sub_typing                            true
% 2.98/0.99  --prep_gs_sim                           true
% 2.98/0.99  --prep_unflatten                        true
% 2.98/0.99  --prep_res_sim                          true
% 2.98/0.99  --prep_upred                            true
% 2.98/0.99  --prep_sem_filter                       exhaustive
% 2.98/0.99  --prep_sem_filter_out                   false
% 2.98/0.99  --pred_elim                             true
% 2.98/0.99  --res_sim_input                         true
% 2.98/0.99  --eq_ax_congr_red                       true
% 2.98/0.99  --pure_diseq_elim                       true
% 2.98/0.99  --brand_transform                       false
% 2.98/0.99  --non_eq_to_eq                          false
% 2.98/0.99  --prep_def_merge                        true
% 2.98/0.99  --prep_def_merge_prop_impl              false
% 2.98/0.99  --prep_def_merge_mbd                    true
% 2.98/0.99  --prep_def_merge_tr_red                 false
% 2.98/0.99  --prep_def_merge_tr_cl                  false
% 2.98/0.99  --smt_preprocessing                     true
% 2.98/0.99  --smt_ac_axioms                         fast
% 2.98/0.99  --preprocessed_out                      false
% 2.98/0.99  --preprocessed_stats                    false
% 2.98/0.99  
% 2.98/0.99  ------ Abstraction refinement Options
% 2.98/0.99  
% 2.98/0.99  --abstr_ref                             []
% 2.98/0.99  --abstr_ref_prep                        false
% 2.98/0.99  --abstr_ref_until_sat                   false
% 2.98/0.99  --abstr_ref_sig_restrict                funpre
% 2.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.99  --abstr_ref_under                       []
% 2.98/0.99  
% 2.98/0.99  ------ SAT Options
% 2.98/0.99  
% 2.98/0.99  --sat_mode                              false
% 2.98/0.99  --sat_fm_restart_options                ""
% 2.98/0.99  --sat_gr_def                            false
% 2.98/0.99  --sat_epr_types                         true
% 2.98/0.99  --sat_non_cyclic_types                  false
% 2.98/0.99  --sat_finite_models                     false
% 2.98/0.99  --sat_fm_lemmas                         false
% 2.98/0.99  --sat_fm_prep                           false
% 2.98/0.99  --sat_fm_uc_incr                        true
% 2.98/0.99  --sat_out_model                         small
% 2.98/0.99  --sat_out_clauses                       false
% 2.98/0.99  
% 2.98/0.99  ------ QBF Options
% 2.98/0.99  
% 2.98/0.99  --qbf_mode                              false
% 2.98/0.99  --qbf_elim_univ                         false
% 2.98/0.99  --qbf_dom_inst                          none
% 2.98/0.99  --qbf_dom_pre_inst                      false
% 2.98/0.99  --qbf_sk_in                             false
% 2.98/0.99  --qbf_pred_elim                         true
% 2.98/0.99  --qbf_split                             512
% 2.98/0.99  
% 2.98/0.99  ------ BMC1 Options
% 2.98/0.99  
% 2.98/0.99  --bmc1_incremental                      false
% 2.98/0.99  --bmc1_axioms                           reachable_all
% 2.98/0.99  --bmc1_min_bound                        0
% 2.98/0.99  --bmc1_max_bound                        -1
% 2.98/0.99  --bmc1_max_bound_default                -1
% 2.98/0.99  --bmc1_symbol_reachability              true
% 2.98/0.99  --bmc1_property_lemmas                  false
% 2.98/0.99  --bmc1_k_induction                      false
% 2.98/0.99  --bmc1_non_equiv_states                 false
% 2.98/0.99  --bmc1_deadlock                         false
% 2.98/0.99  --bmc1_ucm                              false
% 2.98/0.99  --bmc1_add_unsat_core                   none
% 2.98/0.99  --bmc1_unsat_core_children              false
% 2.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.99  --bmc1_out_stat                         full
% 2.98/0.99  --bmc1_ground_init                      false
% 2.98/0.99  --bmc1_pre_inst_next_state              false
% 2.98/0.99  --bmc1_pre_inst_state                   false
% 2.98/0.99  --bmc1_pre_inst_reach_state             false
% 2.98/0.99  --bmc1_out_unsat_core                   false
% 2.98/0.99  --bmc1_aig_witness_out                  false
% 2.98/0.99  --bmc1_verbose                          false
% 2.98/0.99  --bmc1_dump_clauses_tptp                false
% 2.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.99  --bmc1_dump_file                        -
% 2.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.99  --bmc1_ucm_extend_mode                  1
% 2.98/0.99  --bmc1_ucm_init_mode                    2
% 2.98/0.99  --bmc1_ucm_cone_mode                    none
% 2.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.99  --bmc1_ucm_relax_model                  4
% 2.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.99  --bmc1_ucm_layered_model                none
% 2.98/0.99  --bmc1_ucm_max_lemma_size               10
% 2.98/0.99  
% 2.98/0.99  ------ AIG Options
% 2.98/0.99  
% 2.98/0.99  --aig_mode                              false
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation Options
% 2.98/0.99  
% 2.98/0.99  --instantiation_flag                    true
% 2.98/0.99  --inst_sos_flag                         false
% 2.98/0.99  --inst_sos_phase                        true
% 2.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel_side                     none
% 2.98/0.99  --inst_solver_per_active                1400
% 2.98/0.99  --inst_solver_calls_frac                1.
% 2.98/0.99  --inst_passive_queue_type               priority_queues
% 2.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.99  --inst_passive_queues_freq              [25;2]
% 2.98/0.99  --inst_dismatching                      true
% 2.98/0.99  --inst_eager_unprocessed_to_passive     true
% 2.98/0.99  --inst_prop_sim_given                   true
% 2.98/0.99  --inst_prop_sim_new                     false
% 2.98/0.99  --inst_subs_new                         false
% 2.98/0.99  --inst_eq_res_simp                      false
% 2.98/0.99  --inst_subs_given                       false
% 2.98/0.99  --inst_orphan_elimination               true
% 2.98/0.99  --inst_learning_loop_flag               true
% 2.98/0.99  --inst_learning_start                   3000
% 2.98/0.99  --inst_learning_factor                  2
% 2.98/0.99  --inst_start_prop_sim_after_learn       3
% 2.98/0.99  --inst_sel_renew                        solver
% 2.98/0.99  --inst_lit_activity_flag                true
% 2.98/0.99  --inst_restr_to_given                   false
% 2.98/0.99  --inst_activity_threshold               500
% 2.98/0.99  --inst_out_proof                        true
% 2.98/0.99  
% 2.98/0.99  ------ Resolution Options
% 2.98/0.99  
% 2.98/0.99  --resolution_flag                       false
% 2.98/0.99  --res_lit_sel                           adaptive
% 2.98/0.99  --res_lit_sel_side                      none
% 2.98/0.99  --res_ordering                          kbo
% 2.98/0.99  --res_to_prop_solver                    active
% 2.98/0.99  --res_prop_simpl_new                    false
% 2.98/0.99  --res_prop_simpl_given                  true
% 2.98/0.99  --res_passive_queue_type                priority_queues
% 2.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.99  --res_passive_queues_freq               [15;5]
% 2.98/0.99  --res_forward_subs                      full
% 2.98/0.99  --res_backward_subs                     full
% 2.98/0.99  --res_forward_subs_resolution           true
% 2.98/0.99  --res_backward_subs_resolution          true
% 2.98/0.99  --res_orphan_elimination                true
% 2.98/0.99  --res_time_limit                        2.
% 2.98/0.99  --res_out_proof                         true
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Options
% 2.98/0.99  
% 2.98/0.99  --superposition_flag                    true
% 2.98/0.99  --sup_passive_queue_type                priority_queues
% 2.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.99  --demod_completeness_check              fast
% 2.98/0.99  --demod_use_ground                      true
% 2.98/0.99  --sup_to_prop_solver                    passive
% 2.98/0.99  --sup_prop_simpl_new                    true
% 2.98/0.99  --sup_prop_simpl_given                  true
% 2.98/0.99  --sup_fun_splitting                     false
% 2.98/0.99  --sup_smt_interval                      50000
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Simplification Setup
% 2.98/0.99  
% 2.98/0.99  --sup_indices_passive                   []
% 2.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_full_bw                           [BwDemod]
% 2.98/0.99  --sup_immed_triv                        [TrivRules]
% 2.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_immed_bw_main                     []
% 2.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  
% 2.98/0.99  ------ Combination Options
% 2.98/0.99  
% 2.98/0.99  --comb_res_mult                         3
% 2.98/0.99  --comb_sup_mult                         2
% 2.98/0.99  --comb_inst_mult                        10
% 2.98/0.99  
% 2.98/0.99  ------ Debug Options
% 2.98/0.99  
% 2.98/0.99  --dbg_backtrace                         false
% 2.98/0.99  --dbg_dump_prop_clauses                 false
% 2.98/0.99  --dbg_dump_prop_clauses_file            -
% 2.98/0.99  --dbg_out_stat                          false
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  ------ Proving...
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  % SZS status Theorem for theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  fof(f13,conjecture,(
% 2.98/0.99    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f14,negated_conjecture,(
% 2.98/0.99    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.98/0.99    inference(negated_conjecture,[],[f13])).
% 2.98/0.99  
% 2.98/0.99  fof(f34,plain,(
% 2.98/0.99    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f14])).
% 2.98/0.99  
% 2.98/0.99  fof(f35,plain,(
% 2.98/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 2.98/0.99    inference(flattening,[],[f34])).
% 2.98/0.99  
% 2.98/0.99  fof(f40,plain,(
% 2.98/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK2),k3_xboole_0(X1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f39,plain,(
% 2.98/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f38,plain,(
% 2.98/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f41,plain,(
% 2.98/0.99    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 2.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f40,f39,f38])).
% 2.98/0.99  
% 2.98/0.99  fof(f60,plain,(
% 2.98/0.99    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 2.98/0.99    inference(cnf_transformation,[],[f41])).
% 2.98/0.99  
% 2.98/0.99  fof(f9,axiom,(
% 2.98/0.99    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f51,plain,(
% 2.98/0.99    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f9])).
% 2.98/0.99  
% 2.98/0.99  fof(f71,plain,(
% 2.98/0.99    m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 2.98/0.99    inference(definition_unfolding,[],[f60,f51])).
% 2.98/0.99  
% 2.98/0.99  fof(f61,plain,(
% 2.98/0.99    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 2.98/0.99    inference(cnf_transformation,[],[f41])).
% 2.98/0.99  
% 2.98/0.99  fof(f70,plain,(
% 2.98/0.99    m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 2.98/0.99    inference(definition_unfolding,[],[f61,f51])).
% 2.98/0.99  
% 2.98/0.99  fof(f4,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f23,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.98/0.99    inference(ennf_transformation,[],[f4])).
% 2.98/0.99  
% 2.98/0.99  fof(f24,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.98/0.99    inference(flattening,[],[f23])).
% 2.98/0.99  
% 2.98/0.99  fof(f45,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f24])).
% 2.98/0.99  
% 2.98/0.99  fof(f5,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f25,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.98/0.99    inference(ennf_transformation,[],[f5])).
% 2.98/0.99  
% 2.98/0.99  fof(f26,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.98/0.99    inference(flattening,[],[f25])).
% 2.98/0.99  
% 2.98/0.99  fof(f46,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f26])).
% 2.98/0.99  
% 2.98/0.99  fof(f59,plain,(
% 2.98/0.99    v2_lattice3(k2_yellow_1(sK0))),
% 2.98/0.99    inference(cnf_transformation,[],[f41])).
% 2.98/0.99  
% 2.98/0.99  fof(f72,plain,(
% 2.98/0.99    v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 2.98/0.99    inference(definition_unfolding,[],[f59,f51])).
% 2.98/0.99  
% 2.98/0.99  fof(f11,axiom,(
% 2.98/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f16,plain,(
% 2.98/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 2.98/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.98/0.99  
% 2.98/0.99  fof(f55,plain,(
% 2.98/0.99    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f16])).
% 2.98/0.99  
% 2.98/0.99  fof(f64,plain,(
% 2.98/0.99    ( ! [X0] : (v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 2.98/0.99    inference(definition_unfolding,[],[f55,f51])).
% 2.98/0.99  
% 2.98/0.99  fof(f10,axiom,(
% 2.98/0.99    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f15,plain,(
% 2.98/0.99    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.98/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.98/0.99  
% 2.98/0.99  fof(f52,plain,(
% 2.98/0.99    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f15])).
% 2.98/0.99  
% 2.98/0.99  fof(f63,plain,(
% 2.98/0.99    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 2.98/0.99    inference(definition_unfolding,[],[f52,f51])).
% 2.98/0.99  
% 2.98/0.99  fof(f6,axiom,(
% 2.98/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f27,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.98/0.99    inference(ennf_transformation,[],[f6])).
% 2.98/0.99  
% 2.98/0.99  fof(f28,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.98/0.99    inference(flattening,[],[f27])).
% 2.98/0.99  
% 2.98/0.99  fof(f47,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f28])).
% 2.98/0.99  
% 2.98/0.99  fof(f7,axiom,(
% 2.98/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (v4_orders_2(X0) => k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3))))))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f29,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) | ~v4_orders_2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.98/0.99    inference(ennf_transformation,[],[f7])).
% 2.98/0.99  
% 2.98/0.99  fof(f30,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.98/0.99    inference(flattening,[],[f29])).
% 2.98/0.99  
% 2.98/0.99  fof(f48,plain,(
% 2.98/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f30])).
% 2.98/0.99  
% 2.98/0.99  fof(f54,plain,(
% 2.98/0.99    ( ! [X0] : (v4_orders_2(k2_yellow_1(X0))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f16])).
% 2.98/0.99  
% 2.98/0.99  fof(f65,plain,(
% 2.98/0.99    ( ! [X0] : (v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 2.98/0.99    inference(definition_unfolding,[],[f54,f51])).
% 2.98/0.99  
% 2.98/0.99  fof(f8,axiom,(
% 2.98/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f31,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 2.98/0.99    inference(ennf_transformation,[],[f8])).
% 2.98/0.99  
% 2.98/0.99  fof(f32,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 2.98/0.99    inference(flattening,[],[f31])).
% 2.98/0.99  
% 2.98/0.99  fof(f36,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 2.98/0.99    inference(nnf_transformation,[],[f32])).
% 2.98/0.99  
% 2.98/0.99  fof(f50,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f53,plain,(
% 2.98/0.99    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f16])).
% 2.98/0.99  
% 2.98/0.99  fof(f66,plain,(
% 2.98/0.99    ( ! [X0] : (v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 2.98/0.99    inference(definition_unfolding,[],[f53,f51])).
% 2.98/0.99  
% 2.98/0.99  fof(f2,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f19,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.98/0.99    inference(ennf_transformation,[],[f2])).
% 2.98/0.99  
% 2.98/0.99  fof(f20,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.98/0.99    inference(flattening,[],[f19])).
% 2.98/0.99  
% 2.98/0.99  fof(f43,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f20])).
% 2.98/0.99  
% 2.98/0.99  fof(f3,axiom,(
% 2.98/0.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f21,plain,(
% 2.98/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f3])).
% 2.98/0.99  
% 2.98/0.99  fof(f22,plain,(
% 2.98/0.99    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.98/0.99    inference(flattening,[],[f21])).
% 2.98/0.99  
% 2.98/0.99  fof(f44,plain,(
% 2.98/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f22])).
% 2.98/0.99  
% 2.98/0.99  fof(f49,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f12,axiom,(
% 2.98/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f33,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f12])).
% 2.98/0.99  
% 2.98/0.99  fof(f37,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.98/0.99    inference(nnf_transformation,[],[f33])).
% 2.98/0.99  
% 2.98/0.99  fof(f56,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f37])).
% 2.98/0.99  
% 2.98/0.99  fof(f68,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 2.98/0.99    inference(definition_unfolding,[],[f56,f51,f51,f51])).
% 2.98/0.99  
% 2.98/0.99  fof(f58,plain,(
% 2.98/0.99    ~v1_xboole_0(sK0)),
% 2.98/0.99    inference(cnf_transformation,[],[f41])).
% 2.98/0.99  
% 2.98/0.99  fof(f1,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f17,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.98/0.99    inference(ennf_transformation,[],[f1])).
% 2.98/0.99  
% 2.98/0.99  fof(f18,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.98/0.99    inference(flattening,[],[f17])).
% 2.98/0.99  
% 2.98/0.99  fof(f42,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f18])).
% 2.98/0.99  
% 2.98/0.99  fof(f62,plain,(
% 2.98/0.99    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 2.98/0.99    inference(cnf_transformation,[],[f41])).
% 2.98/0.99  
% 2.98/0.99  fof(f69,plain,(
% 2.98/0.99    ~r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 2.98/0.99    inference(definition_unfolding,[],[f62,f51])).
% 2.98/0.99  
% 2.98/0.99  cnf(c_17,negated_conjecture,
% 2.98/0.99      ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 2.98/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_939,negated_conjecture,
% 2.98/0.99      ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1249,plain,
% 2.98/0.99      ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_16,negated_conjecture,
% 2.98/0.99      ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 2.98/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_940,negated_conjecture,
% 2.98/0.99      ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1248,plain,
% 2.98/0.99      ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.98/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.98/0.99      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.98/0.99      | ~ l1_orders_2(X1) ),
% 2.98/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_943,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_49))
% 2.98/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_49))
% 2.98/0.99      | m1_subset_1(k11_lattice3(X0_49,X1_47,X0_47),u1_struct_0(X0_49))
% 2.98/0.99      | ~ l1_orders_2(X0_49) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1245,plain,
% 2.98/0.99      ( m1_subset_1(X0_47,u1_struct_0(X0_49)) != iProver_top
% 2.98/0.99      | m1_subset_1(X1_47,u1_struct_0(X0_49)) != iProver_top
% 2.98/0.99      | m1_subset_1(k11_lattice3(X0_49,X0_47,X1_47),u1_struct_0(X0_49)) = iProver_top
% 2.98/0.99      | l1_orders_2(X0_49) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.98/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.98/0.99      | ~ v5_orders_2(X1)
% 2.98/0.99      | ~ v2_lattice3(X1)
% 2.98/0.99      | ~ l1_orders_2(X1)
% 2.98/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_18,negated_conjecture,
% 2.98/0.99      ( v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 2.98/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_676,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.98/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.98/0.99      | ~ v5_orders_2(X1)
% 2.98/0.99      | ~ l1_orders_2(X1)
% 2.98/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 2.98/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_18]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_677,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_676]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_10,plain,
% 2.98/0.99      ( v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 2.98/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_38,plain,
% 2.98/0.99      ( v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_9,plain,
% 2.98/0.99      ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 2.98/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_41,plain,
% 2.98/0.99      ( l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_681,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_677,c_38,c_41]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_682,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_681]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_936,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X0_47) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_682]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1252,plain,
% 2.98/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47)
% 2.98/0.99      | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1684,plain,
% 2.98/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47)
% 2.98/0.99      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1245,c_1252]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_40,plain,
% 2.98/0.99      ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_42,plain,
% 2.98/0.99      ( l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) = iProver_top ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_40]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3591,plain,
% 2.98/0.99      ( m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47) ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_1684,c_42]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3592,plain,
% 2.98/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47)
% 2.98/0.99      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_3591]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3601,plain,
% 2.98/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47),X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47),X1_47)
% 2.98/0.99      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1248,c_3592]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3797,plain,
% 2.98/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1),X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1),X0_47)
% 2.98/0.99      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1249,c_3601]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.98/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.98/0.99      | ~ v5_orders_2(X1)
% 2.98/0.99      | ~ v2_lattice3(X1)
% 2.98/0.99      | ~ l1_orders_2(X1)
% 2.98/0.99      | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_655,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.98/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.98/0.99      | ~ v5_orders_2(X1)
% 2.98/0.99      | ~ l1_orders_2(X1)
% 2.98/0.99      | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0)
% 2.98/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_656,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_655]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_660,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_656,c_38,c_41]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_661,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_660]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_937,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X0_47) ),
% 2.98/0.99      inference(subtyping,[status(esa)],[c_661]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1251,plain,
% 2.98/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X0_47)
% 2.98/0.99      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/0.99      | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1406,plain,
% 2.98/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47)
% 2.98/0.99      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1248,c_1251]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1476,plain,
% 2.98/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1249,c_1406]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3811,plain,
% 2.98/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47)
% 2.98/0.99      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/0.99      inference(light_normalisation,[status(thm)],[c_3797,c_1476]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4122,plain,
% 2.98/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_1249,c_3811]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.98/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.98/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.98/0.99      | ~ v4_orders_2(X1)
% 2.98/0.99      | ~ v5_orders_2(X1)
% 2.98/0.99      | ~ v2_lattice3(X1)
% 2.98/0.99      | ~ l1_orders_2(X1)
% 2.98/0.99      | k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3) = k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_631,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.98/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.98/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.98/0.99      | ~ v4_orders_2(X1)
% 2.98/0.99      | ~ v5_orders_2(X1)
% 2.98/0.99      | ~ l1_orders_2(X1)
% 2.98/0.99      | k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) = k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3)
% 2.98/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_632,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/0.99      | ~ v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/0.99      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_631]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_11,plain,
% 2.98/1.00      ( v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 2.98/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_35,plain,
% 2.98/1.00      ( v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_636,plain,
% 2.98/1.00      ( ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_632,c_35,c_38,c_41]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_637,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X0),X1) ),
% 2.98/1.00      inference(renaming,[status(thm)],[c_636]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_938,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2_47,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2_47,X0_47),X1_47) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_637]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1250,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1_47,X2_47)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47),X2_47)
% 2.98/1.00      | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/1.00      | m1_subset_1(X2_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/1.00      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2032,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0_47),X1_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47))
% 2.98/1.00      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/1.00      | m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1249,c_1250]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2367,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47)
% 2.98/1.00      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1248,c_2032]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2399,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1249,c_2367]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2410,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_2399,c_1476]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_7,plain,
% 2.98/1.00      ( ~ r3_orders_2(X0,X1,X2)
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | ~ v5_orders_2(X0)
% 2.98/1.00      | ~ v2_lattice3(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0)
% 2.98/1.00      | k12_lattice3(X0,X1,X2) = X1 ),
% 2.98/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_607,plain,
% 2.98/1.00      ( ~ r3_orders_2(X0,X1,X2)
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | ~ v5_orders_2(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0)
% 2.98/1.00      | k12_lattice3(X0,X1,X2) = X1
% 2.98/1.00      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_608,plain,
% 2.98/1.00      ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/1.00      | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/1.00      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_607]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_12,plain,
% 2.98/1.00      ( v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 2.98/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_32,plain,
% 2.98/1.00      ( v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_612,plain,
% 2.98/1.00      ( ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_608,c_32,c_38,c_41]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_613,plain,
% 2.98/1.00      ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
% 2.98/1.00      inference(renaming,[status(thm)],[c_612]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1,plain,
% 2.98/1.00      ( r3_orders_2(X0,X1,X1)
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | v2_struct_0(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2,plain,
% 2.98/1.00      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_227,plain,
% 2.98/1.00      ( r3_orders_2(X0,X1,X1)
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | ~ v2_lattice3(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0) ),
% 2.98/1.00      inference(resolution,[status(thm)],[c_1,c_2]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_566,plain,
% 2.98/1.00      ( r3_orders_2(X0,X1,X1)
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0)
% 2.98/1.00      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_227,c_18]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_567,plain,
% 2.98/1.00      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/1.00      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_566]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_571,plain,
% 2.98/1.00      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_567,c_32,c_41]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_572,plain,
% 2.98/1.00      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 2.98/1.00      inference(renaming,[status(thm)],[c_571]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_778,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | X1 != X0
% 2.98/1.00      | X1 != X2
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X0) = X2
% 2.98/1.00      | g1_orders_2(sK0,k1_yellow_1(sK0)) != g1_orders_2(sK0,k1_yellow_1(sK0)) ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_613,c_572]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_779,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0 ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_778]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_933,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47 ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_779]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_946,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47
% 2.98/1.00      | ~ sP1_iProver_split ),
% 2.98/1.00      inference(splitting,
% 2.98/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.98/1.00                [c_933]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1256,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47
% 2.98/1.00      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/1.00      | sP1_iProver_split != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_22,plain,
% 2.98/1.00      ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_947,plain,
% 2.98/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 2.98/1.00      inference(splitting,
% 2.98/1.00                [splitting(split),new_symbols(definition,[])],
% 2.98/1.00                [c_933]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_988,plain,
% 2.98/1.00      ( sP1_iProver_split = iProver_top
% 2.98/1.00      | sP0_iProver_split = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_989,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47
% 2.98/1.00      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/1.00      | sP1_iProver_split != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_945,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ sP0_iProver_split ),
% 2.98/1.00      inference(splitting,
% 2.98/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.98/1.00                [c_933]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_992,plain,
% 2.98/1.00      ( m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/1.00      | sP0_iProver_split != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_994,plain,
% 2.98/1.00      ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/1.00      | sP0_iProver_split != iProver_top ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_992]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2927,plain,
% 2.98/1.00      ( m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47 ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_1256,c_22,c_988,c_989,c_994]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2928,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X0_47) = X0_47
% 2.98/1.00      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/1.00      inference(renaming,[status(thm)],[c_2927]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2934,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = sK1 ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1249,c_2928]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1559,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0_47)
% 2.98/1.00      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1249,c_1252]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1939,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1249,c_1559]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3137,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = sK1 ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_2934,c_1939]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2368,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0_47)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1),X0_47)
% 2.98/1.00      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1249,c_2032]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2552,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1),sK2) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1248,c_2368]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3319,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_3137,c_2552]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3878,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_2410,c_3319]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_4133,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_4122,c_3878]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_952,plain,
% 2.98/1.00      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.98/1.00      theory(equality) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2358,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != X0_47
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) != X0_47
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_952]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3423,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_2358]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2933,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = sK2 ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1248,c_2928]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1558,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0_47)
% 2.98/1.00      | m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1248,c_1252]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1812,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1248,c_1558]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3061,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = sK2 ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_2933,c_1812]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2398,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1248,c_2367]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3236,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 2.98/1.00      inference(demodulation,[status(thm)],[c_3061,c_2398]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_8,plain,
% 2.98/1.00      ( r3_orders_2(X0,X1,X2)
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | ~ v5_orders_2(X0)
% 2.98/1.00      | ~ v2_lattice3(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0)
% 2.98/1.00      | k12_lattice3(X0,X1,X2) != X1 ),
% 2.98/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_587,plain,
% 2.98/1.00      ( r3_orders_2(X0,X1,X2)
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | ~ v5_orders_2(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0)
% 2.98/1.00      | k12_lattice3(X0,X1,X2) != X1
% 2.98/1.00      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_588,plain,
% 2.98/1.00      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/1.00      | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/1.00      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_587]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_590,plain,
% 2.98/1.00      ( ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_588,c_32,c_38,c_41]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_591,plain,
% 2.98/1.00      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
% 2.98/1.00      inference(renaming,[status(thm)],[c_590]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_14,plain,
% 2.98/1.00      ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 2.98/1.00      | r1_tarski(X1,X2)
% 2.98/1.00      | v1_xboole_0(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_19,negated_conjecture,
% 2.98/1.00      ( ~ v1_xboole_0(sK0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_290,plain,
% 2.98/1.00      ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
% 2.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 2.98/1.00      | r1_tarski(X1,X2)
% 2.98/1.00      | sK0 != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_291,plain,
% 2.98/1.00      ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | r1_tarski(X0,X1) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_290]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_743,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | r1_tarski(X0,X1)
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
% 2.98/1.00      inference(resolution,[status(thm)],[c_591,c_291]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_935,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | r1_tarski(X0_47,X1_47)
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0_47,X1_47) != X0_47 ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_743]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2655,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47)
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0_47) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_935]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2657,plain,
% 2.98/1.00      ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_2655]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2329,plain,
% 2.98/1.00      ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_936]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1856,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != X0_47
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) != X0_47 ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_952]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2328,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1856]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1489,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != X0_47
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) != X0_47 ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_952]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1669,plain,
% 2.98/1.00      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)
% 2.98/1.00      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1489]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1395,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(g1_orders_2(X0_50,k1_yellow_1(X0_50))))
% 2.98/1.00      | ~ m1_subset_1(X1_47,u1_struct_0(g1_orders_2(X0_50,k1_yellow_1(X0_50))))
% 2.98/1.00      | m1_subset_1(k11_lattice3(g1_orders_2(X0_50,k1_yellow_1(X0_50)),X0_47,X1_47),u1_struct_0(g1_orders_2(X0_50,k1_yellow_1(X0_50))))
% 2.98/1.00      | ~ l1_orders_2(g1_orders_2(X0_50,k1_yellow_1(X0_50))) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_943]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1469,plain,
% 2.98/1.00      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1395]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1420,plain,
% 2.98/1.00      ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 2.98/1.00      | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
% 2.98/1.00      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_935]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1417,plain,
% 2.98/1.00      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)
% 2.98/1.00      | m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1406]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_0,plain,
% 2.98/1.00      ( ~ r1_tarski(X0,X1)
% 2.98/1.00      | ~ r1_tarski(X0,X2)
% 2.98/1.00      | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 2.98/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_944,plain,
% 2.98/1.00      ( ~ r1_tarski(X0_47,X1_47)
% 2.98/1.00      | ~ r1_tarski(X0_47,X2_47)
% 2.98/1.00      | r1_tarski(X0_47,k3_xboole_0(X2_47,X1_47)) ),
% 2.98/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1387,plain,
% 2.98/1.00      ( r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k3_xboole_0(sK1,sK2))
% 2.98/1.00      | ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
% 2.98/1.00      | ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_944]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_15,negated_conjecture,
% 2.98/1.00      ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
% 2.98/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(contradiction,plain,
% 2.98/1.00      ( $false ),
% 2.98/1.00      inference(minisat,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_4133,c_3423,c_3236,c_2657,c_2329,c_2328,c_1669,c_1476,
% 2.98/1.00                 c_1469,c_1420,c_1417,c_1387,c_41,c_15,c_16,c_22,c_17]) ).
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  ------                               Statistics
% 2.98/1.00  
% 2.98/1.00  ------ General
% 2.98/1.00  
% 2.98/1.00  abstr_ref_over_cycles:                  0
% 2.98/1.00  abstr_ref_under_cycles:                 0
% 2.98/1.00  gc_basic_clause_elim:                   0
% 2.98/1.00  forced_gc_time:                         0
% 2.98/1.00  parsing_time:                           0.009
% 2.98/1.00  unif_index_cands_time:                  0.
% 2.98/1.00  unif_index_add_time:                    0.
% 2.98/1.00  orderings_time:                         0.
% 2.98/1.00  out_proof_time:                         0.014
% 2.98/1.00  total_time:                             0.18
% 2.98/1.00  num_of_symbols:                         58
% 2.98/1.00  num_of_terms:                           3024
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing
% 2.98/1.00  
% 2.98/1.00  num_of_splits:                          4
% 2.98/1.00  num_of_split_atoms:                     3
% 2.98/1.00  num_of_reused_defs:                     1
% 2.98/1.00  num_eq_ax_congr_red:                    18
% 2.98/1.00  num_of_sem_filtered_clauses:            4
% 2.98/1.00  num_of_subtypes:                        5
% 2.98/1.00  monotx_restored_types:                  0
% 2.98/1.00  sat_num_of_epr_types:                   0
% 2.98/1.00  sat_num_of_non_cyclic_types:            0
% 2.98/1.00  sat_guarded_non_collapsed_types:        1
% 2.98/1.00  num_pure_diseq_elim:                    0
% 2.98/1.00  simp_replaced_by:                       0
% 2.98/1.00  res_preprocessed:                       75
% 2.98/1.00  prep_upred:                             0
% 2.98/1.00  prep_unflattend:                        23
% 2.98/1.00  smt_new_axioms:                         0
% 2.98/1.00  pred_elim_cands:                        3
% 2.98/1.00  pred_elim:                              7
% 2.98/1.00  pred_elim_cl:                           7
% 2.98/1.00  pred_elim_cycles:                       13
% 2.98/1.00  merged_defs:                            0
% 2.98/1.00  merged_defs_ncl:                        0
% 2.98/1.00  bin_hyper_res:                          0
% 2.98/1.00  prep_cycles:                            4
% 2.98/1.00  pred_elim_time:                         0.014
% 2.98/1.00  splitting_time:                         0.
% 2.98/1.00  sem_filter_time:                        0.
% 2.98/1.00  monotx_time:                            0.
% 2.98/1.00  subtype_inf_time:                       0.
% 2.98/1.00  
% 2.98/1.00  ------ Problem properties
% 2.98/1.00  
% 2.98/1.00  clauses:                                17
% 2.98/1.00  conjectures:                            3
% 2.98/1.00  epr:                                    2
% 2.98/1.00  horn:                                   15
% 2.98/1.00  ground:                                 5
% 2.98/1.00  unary:                                  4
% 2.98/1.00  binary:                                 4
% 2.98/1.00  lits:                                   43
% 2.98/1.00  lits_eq:                                6
% 2.98/1.00  fd_pure:                                0
% 2.98/1.00  fd_pseudo:                              0
% 2.98/1.00  fd_cond:                                0
% 2.98/1.00  fd_pseudo_cond:                         0
% 2.98/1.00  ac_symbols:                             0
% 2.98/1.00  
% 2.98/1.00  ------ Propositional Solver
% 2.98/1.00  
% 2.98/1.00  prop_solver_calls:                      29
% 2.98/1.00  prop_fast_solver_calls:                 751
% 2.98/1.00  smt_solver_calls:                       0
% 2.98/1.00  smt_fast_solver_calls:                  0
% 2.98/1.00  prop_num_of_clauses:                    1309
% 2.98/1.00  prop_preprocess_simplified:             3777
% 2.98/1.00  prop_fo_subsumed:                       45
% 2.98/1.00  prop_solver_time:                       0.
% 2.98/1.00  smt_solver_time:                        0.
% 2.98/1.00  smt_fast_solver_time:                   0.
% 2.98/1.00  prop_fast_solver_time:                  0.
% 2.98/1.00  prop_unsat_core_time:                   0.
% 2.98/1.00  
% 2.98/1.00  ------ QBF
% 2.98/1.00  
% 2.98/1.00  qbf_q_res:                              0
% 2.98/1.00  qbf_num_tautologies:                    0
% 2.98/1.00  qbf_prep_cycles:                        0
% 2.98/1.00  
% 2.98/1.00  ------ BMC1
% 2.98/1.00  
% 2.98/1.00  bmc1_current_bound:                     -1
% 2.98/1.00  bmc1_last_solved_bound:                 -1
% 2.98/1.00  bmc1_unsat_core_size:                   -1
% 2.98/1.00  bmc1_unsat_core_parents_size:           -1
% 2.98/1.00  bmc1_merge_next_fun:                    0
% 2.98/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.98/1.00  
% 2.98/1.00  ------ Instantiation
% 2.98/1.00  
% 2.98/1.00  inst_num_of_clauses:                    407
% 2.98/1.00  inst_num_in_passive:                    110
% 2.98/1.00  inst_num_in_active:                     249
% 2.98/1.00  inst_num_in_unprocessed:                48
% 2.98/1.00  inst_num_of_loops:                      280
% 2.98/1.00  inst_num_of_learning_restarts:          0
% 2.98/1.00  inst_num_moves_active_passive:          26
% 2.98/1.00  inst_lit_activity:                      0
% 2.98/1.00  inst_lit_activity_moves:                0
% 2.98/1.00  inst_num_tautologies:                   0
% 2.98/1.00  inst_num_prop_implied:                  0
% 2.98/1.00  inst_num_existing_simplified:           0
% 2.98/1.00  inst_num_eq_res_simplified:             0
% 2.98/1.00  inst_num_child_elim:                    0
% 2.98/1.00  inst_num_of_dismatching_blockings:      146
% 2.98/1.00  inst_num_of_non_proper_insts:           607
% 2.98/1.00  inst_num_of_duplicates:                 0
% 2.98/1.00  inst_inst_num_from_inst_to_res:         0
% 2.98/1.00  inst_dismatching_checking_time:         0.
% 2.98/1.00  
% 2.98/1.00  ------ Resolution
% 2.98/1.00  
% 2.98/1.00  res_num_of_clauses:                     0
% 2.98/1.00  res_num_in_passive:                     0
% 2.98/1.00  res_num_in_active:                      0
% 2.98/1.00  res_num_of_loops:                       79
% 2.98/1.00  res_forward_subset_subsumed:            69
% 2.98/1.00  res_backward_subset_subsumed:           0
% 2.98/1.00  res_forward_subsumed:                   0
% 2.98/1.00  res_backward_subsumed:                  0
% 2.98/1.00  res_forward_subsumption_resolution:     4
% 2.98/1.00  res_backward_subsumption_resolution:    0
% 2.98/1.00  res_clause_to_clause_subsumption:       366
% 2.98/1.00  res_orphan_elimination:                 0
% 2.98/1.00  res_tautology_del:                      54
% 2.98/1.00  res_num_eq_res_simplified:              0
% 2.98/1.00  res_num_sel_changes:                    0
% 2.98/1.00  res_moves_from_active_to_pass:          0
% 2.98/1.00  
% 2.98/1.00  ------ Superposition
% 2.98/1.00  
% 2.98/1.00  sup_time_total:                         0.
% 2.98/1.00  sup_time_generating:                    0.
% 2.98/1.00  sup_time_sim_full:                      0.
% 2.98/1.00  sup_time_sim_immed:                     0.
% 2.98/1.00  
% 2.98/1.00  sup_num_of_clauses:                     78
% 2.98/1.00  sup_num_in_active:                      48
% 2.98/1.00  sup_num_in_passive:                     30
% 2.98/1.00  sup_num_of_loops:                       55
% 2.98/1.00  sup_fw_superposition:                   84
% 2.98/1.00  sup_bw_superposition:                   20
% 2.98/1.00  sup_immediate_simplified:               28
% 2.98/1.00  sup_given_eliminated:                   0
% 2.98/1.00  comparisons_done:                       0
% 2.98/1.00  comparisons_avoided:                    0
% 2.98/1.00  
% 2.98/1.00  ------ Simplifications
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  sim_fw_subset_subsumed:                 6
% 2.98/1.00  sim_bw_subset_subsumed:                 0
% 2.98/1.00  sim_fw_subsumed:                        6
% 2.98/1.00  sim_bw_subsumed:                        0
% 2.98/1.00  sim_fw_subsumption_res:                 0
% 2.98/1.00  sim_bw_subsumption_res:                 0
% 2.98/1.00  sim_tautology_del:                      1
% 2.98/1.00  sim_eq_tautology_del:                   9
% 2.98/1.00  sim_eq_res_simp:                        0
% 2.98/1.00  sim_fw_demodulated:                     2
% 2.98/1.00  sim_bw_demodulated:                     8
% 2.98/1.00  sim_light_normalised:                   16
% 2.98/1.00  sim_joinable_taut:                      0
% 2.98/1.00  sim_joinable_simp:                      0
% 2.98/1.00  sim_ac_normalised:                      0
% 2.98/1.00  sim_smt_subsumption:                    0
% 2.98/1.00  
%------------------------------------------------------------------------------
