%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 238 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   27
%              Number of atoms          :  528 (1250 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f449,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f44,f45,f218,f304])).

fof(f304,plain,(
    ! [X0,X1] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f303,f49])).

fof(f49,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X0)
      | ~ l1_orders_2(k2_yellow_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f148,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1) ) ),
    inference(subsumption_resolution,[],[f147,f48])).

fof(f48,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1) ) ),
    inference(subsumption_resolution,[],[f146,f43])).

fof(f43,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ v2_lattice3(k2_yellow_1(sK0))
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1) ) ),
    inference(subsumption_resolution,[],[f145,f49])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ v2_lattice3(k2_yellow_1(sK0))
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ v2_lattice3(k2_yellow_1(sK0))
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(resolution,[],[f135,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(sK0),X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(resolution,[],[f104,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_tarski(X1,X2)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(subsumption_resolution,[],[f103,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0))
      | r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f102,f47])).

fof(f47,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f101,f49])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f134,f65])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f69,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f218,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f214,f96])).

fof(f96,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f214,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(resolution,[],[f202,f46])).

fof(f46,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f202,plain,(
    ! [X4,X5] :
      ( r1_tarski(X4,k3_xboole_0(X5,sK2))
      | ~ r1_tarski(X4,X5)
      | ~ sQ4_eqProxy(X4,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ) ),
    inference(resolution,[],[f190,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f70])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0)
      | r1_tarski(X0,k3_xboole_0(X1,sK2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f162,f44])).

fof(f162,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(k2_yellow_1(sK0)))
      | ~ sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),X7,sK2),X8)
      | r1_tarski(X8,k3_xboole_0(X9,sK2))
      | ~ r1_tarski(X8,X9) ) ),
    inference(resolution,[],[f157,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f157,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK2)
      | ~ sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),X0,sK2),X1)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(resolution,[],[f140,f96])).

fof(f140,plain,(
    ! [X4,X5,X3] :
      ( ~ sQ4_eqProxy(sK2,X4)
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
      | ~ sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),X3,sK2),X5)
      | r1_tarski(X5,X4) ) ),
    inference(resolution,[],[f137,f45])).

fof(f137,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0)))
      | ~ sQ4_eqProxy(X3,X5)
      | ~ sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),X4,X3),X6)
      | r1_tarski(X6,X5) ) ),
    inference(resolution,[],[f133,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ sQ4_eqProxy(X0,X1)
      | r1_tarski(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f70])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f132,f49])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X1)
      | ~ l1_orders_2(k2_yellow_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f126,f65])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0) ) ),
    inference(subsumption_resolution,[],[f125,f48])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0) ) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ v2_lattice3(k2_yellow_1(sK0))
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0) ) ),
    inference(subsumption_resolution,[],[f123,f49])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ v2_lattice3(k2_yellow_1(sK0))
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ v2_lattice3(k2_yellow_1(sK0))
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(resolution,[],[f113,f105])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f112,f65])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f68,f55])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f45,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (9331)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (9330)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (9340)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (9340)Refutation not found, incomplete strategy% (9340)------------------------------
% 0.22/0.49  % (9340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9340)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9340)Memory used [KB]: 1663
% 0.22/0.49  % (9340)Time elapsed: 0.073 s
% 0.22/0.49  % (9340)------------------------------
% 0.22/0.49  % (9340)------------------------------
% 0.22/0.49  % (9329)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (9327)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (9334)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (9327)Refutation not found, incomplete strategy% (9327)------------------------------
% 0.22/0.49  % (9327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9327)Memory used [KB]: 10618
% 0.22/0.49  % (9327)Time elapsed: 0.055 s
% 0.22/0.49  % (9327)------------------------------
% 0.22/0.49  % (9327)------------------------------
% 0.22/0.50  % (9332)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (9331)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f44,f45,f218,f304])).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f303,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X0) | ~l1_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f301])).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f148,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f147,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f146,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v2_lattice3(k2_yellow_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33,f32,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f11])).
% 0.22/0.50  fof(f11,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f145,f49])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f144])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.50    inference(resolution,[],[f135,f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.50    inference(resolution,[],[f104,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r1_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f103,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0)) | r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f102,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f101,f49])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(resolution,[],[f64,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f134,f65])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f69,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(rectify,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f214,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X0] : (sQ4_eqProxy(X0,X0)) )),
% 0.22/0.50    inference(equality_proxy_axiom,[],[f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.50    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.50    inference(resolution,[],[f202,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ( ! [X4,X5] : (r1_tarski(X4,k3_xboole_0(X5,sK2)) | ~r1_tarski(X4,X5) | ~sQ4_eqProxy(X4,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))) )),
% 0.22/0.50    inference(resolution,[],[f190,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sQ4_eqProxy(X1,X0) | ~sQ4_eqProxy(X0,X1)) )),
% 0.22/0.50    inference(equality_proxy_axiom,[],[f70])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0) | r1_tarski(X0,k3_xboole_0(X1,sK2)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f162,f44])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X8,X7,X9] : (~m1_subset_1(X7,u1_struct_0(k2_yellow_1(sK0))) | ~sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),X7,sK2),X8) | r1_tarski(X8,k3_xboole_0(X9,sK2)) | ~r1_tarski(X8,X9)) )),
% 0.22/0.50    inference(resolution,[],[f157,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,sK2) | ~sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),X0,sK2),X1) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.50    inference(resolution,[],[f140,f96])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (~sQ4_eqProxy(sK2,X4) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),X3,sK2),X5) | r1_tarski(X5,X4)) )),
% 0.22/0.50    inference(resolution,[],[f137,f45])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0))) | ~sQ4_eqProxy(X3,X5) | ~sQ4_eqProxy(k11_lattice3(k2_yellow_1(sK0),X4,X3),X6) | r1_tarski(X6,X5)) )),
% 0.22/0.50    inference(resolution,[],[f133,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X2) | ~sQ4_eqProxy(X2,X3) | ~sQ4_eqProxy(X0,X1) | r1_tarski(X1,X3)) )),
% 0.22/0.50    inference(equality_proxy_axiom,[],[f70])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f132,f49])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~l1_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f126,f65])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f125,f48])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f124,f43])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f123,f49])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f122])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X0),X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.50    inference(resolution,[],[f113,f105])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f112,f65])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f68,f55])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (9331)------------------------------
% 0.22/0.50  % (9331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9331)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (9331)Memory used [KB]: 6396
% 0.22/0.50  % (9331)Time elapsed: 0.083 s
% 0.22/0.50  % (9331)------------------------------
% 0.22/0.50  % (9331)------------------------------
% 0.22/0.50  % (9326)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (9336)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (9323)Success in time 0.135 s
%------------------------------------------------------------------------------
