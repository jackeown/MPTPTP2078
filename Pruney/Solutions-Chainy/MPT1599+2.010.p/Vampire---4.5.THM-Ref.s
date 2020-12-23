%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  196 (1490 expanded)
%              Number of leaves         :   21 ( 497 expanded)
%              Depth                    :   36
%              Number of atoms          :  722 (5887 expanded)
%              Number of equality atoms :  103 ( 523 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f810,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f475,f784,f802])).

fof(f802,plain,
    ( spl3_2
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f800,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f42,f41,f40])).

fof(f40,plain,
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

fof(f42,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f800,plain,
    ( v1_xboole_0(sK0)
    | spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f799,f469])).

fof(f469,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl3_12
  <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f799,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f798,f90])).

fof(f90,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_2
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f798,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f795,f75])).

fof(f75,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f50,f56])).

fof(f56,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f795,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_12 ),
    inference(resolution,[],[f762,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f78,f56])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f58,f56])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f762,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f761,f469])).

fof(f761,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(trivial_inequality_removal,[],[f750])).

fof(f750,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f335,f747])).

fof(f747,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f746,f140])).

fof(f140,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    inference(resolution,[],[f136,f75])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0) ) ),
    inference(resolution,[],[f135,f74])).

fof(f74,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f49,f56])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f134,f48])).

fof(f48,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f133,f54])).

fof(f54,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f131,f55])).

fof(f55,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f64,f56])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(f746,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f745,f364])).

fof(f364,plain,(
    sK2 = k11_lattice3(k2_yellow_1(sK0),sK2,sK2) ),
    inference(backward_demodulation,[],[f236,f359])).

fof(f359,plain,(
    sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f357,f75])).

fof(f357,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k12_lattice3(k2_yellow_1(sK0),X0,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f356,f81])).

fof(f81,plain,(
    ~ v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f80,f55])).

fof(f80,plain,
    ( ~ v2_struct_0(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f60,f48])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f356,plain,(
    ! [X0] :
      ( k12_lattice3(k2_yellow_1(sK0),X0,X0) = X0
      | ~ m1_subset_1(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f355,f48])).

fof(f355,plain,(
    ! [X4,X3] :
      ( ~ v2_lattice3(k2_yellow_1(X3))
      | k12_lattice3(k2_yellow_1(X3),X4,X4) = X4
      | ~ m1_subset_1(X4,X3)
      | v2_struct_0(k2_yellow_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,X3)
      | k12_lattice3(k2_yellow_1(X3),X4,X4) = X4
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ m1_subset_1(X4,X3)
      | v2_struct_0(k2_yellow_1(X3)) ) ),
    inference(forward_demodulation,[],[f353,f56])).

fof(f353,plain,(
    ! [X4,X3] :
      ( k12_lattice3(k2_yellow_1(X3),X4,X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ m1_subset_1(X4,X3)
      | v2_struct_0(k2_yellow_1(X3)) ) ),
    inference(subsumption_resolution,[],[f352,f52])).

fof(f52,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f352,plain,(
    ! [X4,X3] :
      ( k12_lattice3(k2_yellow_1(X3),X4,X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ v3_orders_2(k2_yellow_1(X3))
      | ~ m1_subset_1(X4,X3)
      | v2_struct_0(k2_yellow_1(X3)) ) ),
    inference(subsumption_resolution,[],[f351,f54])).

fof(f351,plain,(
    ! [X4,X3] :
      ( k12_lattice3(k2_yellow_1(X3),X4,X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3))
      | ~ v3_orders_2(k2_yellow_1(X3))
      | ~ m1_subset_1(X4,X3)
      | v2_struct_0(k2_yellow_1(X3)) ) ),
    inference(subsumption_resolution,[],[f343,f55])).

fof(f343,plain,(
    ! [X4,X3] :
      ( k12_lattice3(k2_yellow_1(X3),X4,X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3))
      | ~ v3_orders_2(k2_yellow_1(X3))
      | ~ m1_subset_1(X4,X3)
      | v2_struct_0(k2_yellow_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,(
    ! [X4,X3] :
      ( k12_lattice3(k2_yellow_1(X3),X4,X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3)))
      | ~ l1_orders_2(k2_yellow_1(X3))
      | ~ v2_lattice3(k2_yellow_1(X3))
      | ~ v5_orders_2(k2_yellow_1(X3))
      | ~ v3_orders_2(k2_yellow_1(X3))
      | ~ m1_subset_1(X4,X3)
      | v2_struct_0(k2_yellow_1(X3)) ) ),
    inference(resolution,[],[f63,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X1)
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(forward_demodulation,[],[f114,f56])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f113,f52])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f112,f55])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f68,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f93,f52])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f92,f55])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f61,f56])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | k12_lattice3(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f236,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = k12_lattice3(k2_yellow_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f194,f75])).

fof(f194,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X1,sK2) = k12_lattice3(k2_yellow_1(sK0),X1,sK2) ) ),
    inference(resolution,[],[f192,f75])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k12_lattice3(k2_yellow_1(sK0),X0,X1) ) ),
    inference(resolution,[],[f191,f48])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f190,f54])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f188,f55])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f69,f56])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f745,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f718,f140])).

fof(f718,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
    inference(resolution,[],[f708,f75])).

fof(f708,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X1,sK1)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,X1),sK1) ) ),
    inference(resolution,[],[f703,f75])).

fof(f703,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X1,k11_lattice3(k2_yellow_1(sK0),X0,sK1)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X1,X0),sK1) ) ),
    inference(resolution,[],[f694,f74])).

fof(f694,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,k11_lattice3(k2_yellow_1(sK0),X1,X2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),X2) ) ),
    inference(resolution,[],[f530,f48])).

fof(f530,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f529,f54])).

fof(f529,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f528,f55])).

fof(f528,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f526,f53])).

fof(f53,plain,(
    ! [X0] : v4_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f526,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ v4_orders_2(k2_yellow_1(X0))
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f65,f56])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
                   => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_lattice3)).

fof(f335,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f334,f56])).

fof(f334,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f333,f75])).

fof(f333,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f332,f56])).

fof(f332,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f331,f52])).

fof(f331,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f330,f54])).

fof(f330,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f329,f48])).

fof(f329,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f328,f55])).

fof(f328,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(superposition,[],[f62,f319])).

fof(f319,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f318,f173])).

fof(f173,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f171,f140])).

fof(f171,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
    inference(resolution,[],[f167,f75])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,sK1)) ) ),
    inference(resolution,[],[f146,f74])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,X1))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f137,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f98,f55])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f70,f56])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f137,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,X1) ) ),
    inference(resolution,[],[f135,f75])).

fof(f318,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f315,f140])).

fof(f315,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) ),
    inference(resolution,[],[f311,f75])).

fof(f311,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK2) ) ),
    inference(resolution,[],[f237,f74])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f194,f100])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) != X1
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f784,plain,
    ( spl3_1
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f783])).

fof(f783,plain,
    ( $false
    | spl3_1
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f782,f47])).

fof(f782,plain,
    ( v1_xboole_0(sK0)
    | spl3_1
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f781,f469])).

fof(f781,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | spl3_1
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f780,f86])).

fof(f86,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_1
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f780,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f777,f74])).

fof(f777,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_12 ),
    inference(resolution,[],[f735,f79])).

fof(f735,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f734,f469])).

fof(f734,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f725])).

fof(f725,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f297,f723])).

fof(f723,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(backward_demodulation,[],[f154,f722])).

fof(f722,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f721,f140])).

fof(f721,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(forward_demodulation,[],[f717,f361])).

fof(f361,plain,(
    sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
    inference(backward_demodulation,[],[f196,f358])).

fof(f358,plain,(
    sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
    inference(resolution,[],[f357,f74])).

fof(f196,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
    inference(resolution,[],[f193,f74])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k12_lattice3(k2_yellow_1(sK0),X0,sK1) ) ),
    inference(resolution,[],[f192,f74])).

fof(f717,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK1)) ),
    inference(resolution,[],[f708,f74])).

fof(f154,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f152,f140])).

fof(f152,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
    inference(resolution,[],[f148,f75])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,sK1)) ) ),
    inference(resolution,[],[f141,f74])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f136,f100])).

fof(f297,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f296,f56])).

fof(f296,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f295,f74])).

fof(f295,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f294,f56])).

fof(f294,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f293,f52])).

fof(f293,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f292,f54])).

fof(f292,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f291,f48])).

fof(f291,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f290,f55])).

fof(f290,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(superposition,[],[f62,f281])).

fof(f281,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f280,f154])).

fof(f280,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f277,f140])).

fof(f277,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) ),
    inference(resolution,[],[f273,f75])).

fof(f273,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK1) ) ),
    inference(resolution,[],[f198,f74])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK1)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f193,f100])).

fof(f475,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl3_12 ),
    inference(subsumption_resolution,[],[f473,f74])).

fof(f473,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl3_12 ),
    inference(subsumption_resolution,[],[f472,f75])).

fof(f472,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | spl3_12 ),
    inference(resolution,[],[f470,f100])).

fof(f470,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f468])).

fof(f91,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f88,f84])).

fof(f82,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(resolution,[],[f73,f72])).

fof(f72,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f66,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f66])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:04:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (26233)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (26237)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (26243)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (26229)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (26231)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (26236)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (26227)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (26232)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (26228)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (26240)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (26244)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (26234)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (26235)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (26238)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (26239)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (26238)Refutation not found, incomplete strategy% (26238)------------------------------
% 0.22/0.50  % (26238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26238)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26238)Memory used [KB]: 10618
% 0.22/0.50  % (26238)Time elapsed: 0.086 s
% 0.22/0.50  % (26238)------------------------------
% 0.22/0.50  % (26238)------------------------------
% 0.22/0.50  % (26230)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (26241)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (26242)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (26236)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f810,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f91,f475,f784,f802])).
% 0.22/0.51  fof(f802,plain,(
% 0.22/0.51    spl3_2 | ~spl3_12),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f801])).
% 0.22/0.51  fof(f801,plain,(
% 0.22/0.51    $false | (spl3_2 | ~spl3_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f800,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f42,f41,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f15])).
% 0.22/0.51  fof(f15,conjecture,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.22/0.51  fof(f800,plain,(
% 0.22/0.51    v1_xboole_0(sK0) | (spl3_2 | ~spl3_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f799,f469])).
% 0.22/0.51  fof(f469,plain,(
% 0.22/0.51    m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~spl3_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f468])).
% 0.22/0.51  fof(f468,plain,(
% 0.22/0.51    spl3_12 <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.51  fof(f799,plain,(
% 0.22/0.51    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | (spl3_2 | ~spl3_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f798,f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl3_2 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f798,plain,(
% 0.22/0.51    r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | ~spl3_12),
% 0.22/0.51    inference(subsumption_resolution,[],[f795,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    m1_subset_1(sK2,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f50,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f795,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,sK0) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | ~spl3_12),
% 0.22/0.51    inference(resolution,[],[f762,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f78,f56])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f58,f56])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.22/0.51  fof(f762,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~spl3_12),
% 0.22/0.51    inference(subsumption_resolution,[],[f761,f469])).
% 0.22/0.51  fof(f761,plain,(
% 0.22/0.51    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f750])).
% 0.22/0.51  fof(f750,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.22/0.51    inference(backward_demodulation,[],[f335,f747])).
% 0.22/0.51  fof(f747,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f746,f140])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.22/0.51    inference(resolution,[],[f136,f75])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)) )),
% 0.22/0.51    inference(resolution,[],[f135,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    m1_subset_1(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f49,f56])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f134,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    v2_lattice3(k2_yellow_1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X0)) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f131,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(superposition,[],[f64,f56])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).
% 0.22/0.51  fof(f746,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f745,f364])).
% 0.22/0.51  fof(f364,plain,(
% 0.22/0.51    sK2 = k11_lattice3(k2_yellow_1(sK0),sK2,sK2)),
% 0.22/0.51    inference(backward_demodulation,[],[f236,f359])).
% 0.22/0.51  fof(f359,plain,(
% 0.22/0.51    sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,sK2)),
% 0.22/0.51    inference(resolution,[],[f357,f75])).
% 0.22/0.51  fof(f357,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,sK0) | k12_lattice3(k2_yellow_1(sK0),X0,X0) = X0) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f356,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ~v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f80,f55])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ~v2_struct_0(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(resolution,[],[f60,f48])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.22/0.51  fof(f356,plain,(
% 0.22/0.51    ( ! [X0] : (k12_lattice3(k2_yellow_1(sK0),X0,X0) = X0 | ~m1_subset_1(X0,sK0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f355,f48])).
% 0.22/0.51  fof(f355,plain,(
% 0.22/0.51    ( ! [X4,X3] : (~v2_lattice3(k2_yellow_1(X3)) | k12_lattice3(k2_yellow_1(X3),X4,X4) = X4 | ~m1_subset_1(X4,X3) | v2_struct_0(k2_yellow_1(X3))) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f354])).
% 0.22/0.51  fof(f354,plain,(
% 0.22/0.51    ( ! [X4,X3] : (~m1_subset_1(X4,X3) | k12_lattice3(k2_yellow_1(X3),X4,X4) = X4 | ~v2_lattice3(k2_yellow_1(X3)) | ~m1_subset_1(X4,X3) | v2_struct_0(k2_yellow_1(X3))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f353,f56])).
% 0.22/0.51  fof(f353,plain,(
% 0.22/0.51    ( ! [X4,X3] : (k12_lattice3(k2_yellow_1(X3),X4,X4) = X4 | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~v2_lattice3(k2_yellow_1(X3)) | ~m1_subset_1(X4,X3) | v2_struct_0(k2_yellow_1(X3))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f352,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f352,plain,(
% 0.22/0.51    ( ! [X4,X3] : (k12_lattice3(k2_yellow_1(X3),X4,X4) = X4 | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~v2_lattice3(k2_yellow_1(X3)) | ~v3_orders_2(k2_yellow_1(X3)) | ~m1_subset_1(X4,X3) | v2_struct_0(k2_yellow_1(X3))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f351,f54])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    ( ! [X4,X3] : (k12_lattice3(k2_yellow_1(X3),X4,X4) = X4 | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~v2_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3)) | ~v3_orders_2(k2_yellow_1(X3)) | ~m1_subset_1(X4,X3) | v2_struct_0(k2_yellow_1(X3))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f343,f55])).
% 0.22/0.51  fof(f343,plain,(
% 0.22/0.51    ( ! [X4,X3] : (k12_lattice3(k2_yellow_1(X3),X4,X4) = X4 | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~l1_orders_2(k2_yellow_1(X3)) | ~v2_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3)) | ~v3_orders_2(k2_yellow_1(X3)) | ~m1_subset_1(X4,X3) | v2_struct_0(k2_yellow_1(X3))) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f342])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    ( ! [X4,X3] : (k12_lattice3(k2_yellow_1(X3),X4,X4) = X4 | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(X3))) | ~l1_orders_2(k2_yellow_1(X3)) | ~v2_lattice3(k2_yellow_1(X3)) | ~v5_orders_2(k2_yellow_1(X3)) | ~v3_orders_2(k2_yellow_1(X3)) | ~m1_subset_1(X4,X3) | v2_struct_0(k2_yellow_1(X3))) )),
% 0.22/0.51    inference(resolution,[],[f63,f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X1) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r3_orders_2(k2_yellow_1(X0),X1,X1) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f114,f56])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f113,f52])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f112,f55])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f109])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(resolution,[],[f68,f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X1) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f93,f52])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r1_orders_2(k2_yellow_1(X0),X1,X1) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f92,f55])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r1_orders_2(k2_yellow_1(X0),X1,X1) | ~l1_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(superposition,[],[f61,f56])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = k12_lattice3(k2_yellow_1(sK0),sK2,sK2)),
% 0.22/0.51    inference(resolution,[],[f194,f75])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),X1,sK2) = k12_lattice3(k2_yellow_1(sK0),X1,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f192,f75])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k12_lattice3(k2_yellow_1(sK0),X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f191,f48])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X0)) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f190,f54])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f188,f55])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(superposition,[],[f69,f56])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.22/0.51  fof(f745,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f718,f140])).
% 0.22/0.51  fof(f718,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK2,sK1))),
% 0.22/0.51    inference(resolution,[],[f708,f75])).
% 0.22/0.51  fof(f708,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X1,sK1)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,X1),sK1)) )),
% 0.22/0.51    inference(resolution,[],[f703,f75])).
% 0.22/0.51  fof(f703,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X1,k11_lattice3(k2_yellow_1(sK0),X0,sK1)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X1,X0),sK1)) )),
% 0.22/0.51    inference(resolution,[],[f694,f74])).
% 0.22/0.51  fof(f694,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,k11_lattice3(k2_yellow_1(sK0),X1,X2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),X2)) )),
% 0.22/0.51    inference(resolution,[],[f530,f48])).
% 0.22/0.51  fof(f530,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~v2_lattice3(k2_yellow_1(X0)) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f529,f54])).
% 0.22/0.51  fof(f529,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f528,f55])).
% 0.22/0.51  fof(f528,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f526,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0] : (v4_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f526,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,X0) | ~v4_orders_2(k2_yellow_1(X0)) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(superposition,[],[f65,f56])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_orders_2(X0) | k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (v4_orders_2(X0) => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_lattice3)).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.22/0.51    inference(forward_demodulation,[],[f334,f56])).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f333,f75])).
% 0.22/0.51  fof(f333,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,sK0) | k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f332,f56])).
% 0.22/0.51  fof(f332,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f331,f52])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f330,f54])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f329,f48])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f328,f55])).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(superposition,[],[f62,f319])).
% 0.22/0.51  fof(f319,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.22/0.51    inference(forward_demodulation,[],[f318,f173])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f171,f140])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK2,sK1))),
% 0.22/0.51    inference(resolution,[],[f167,f75])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,sK1))) )),
% 0.22/0.51    inference(resolution,[],[f146,f74])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f137,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f98,f55])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(superposition,[],[f70,f56])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),X1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,X1)) )),
% 0.22/0.52    inference(resolution,[],[f135,f75])).
% 0.22/0.52  fof(f318,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f315,f140])).
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK2)),
% 0.22/0.52    inference(resolution,[],[f311,f75])).
% 0.22/0.52  fof(f311,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK2)) )),
% 0.22/0.52    inference(resolution,[],[f237,f74])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2) | ~m1_subset_1(X0,sK0)) )),
% 0.22/0.52    inference(resolution,[],[f194,f100])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f784,plain,(
% 0.22/0.52    spl3_1 | ~spl3_12),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f783])).
% 0.22/0.52  fof(f783,plain,(
% 0.22/0.52    $false | (spl3_1 | ~spl3_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f782,f47])).
% 0.22/0.52  fof(f782,plain,(
% 0.22/0.52    v1_xboole_0(sK0) | (spl3_1 | ~spl3_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f781,f469])).
% 0.22/0.52  fof(f781,plain,(
% 0.22/0.52    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | (spl3_1 | ~spl3_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f780,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl3_1 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f780,plain,(
% 0.22/0.52    r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | ~spl3_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f777,f74])).
% 0.22/0.52  fof(f777,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,sK0) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | ~spl3_12),
% 0.22/0.52    inference(resolution,[],[f735,f79])).
% 0.22/0.52  fof(f735,plain,(
% 0.22/0.52    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~spl3_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f734,f469])).
% 0.22/0.52  fof(f734,plain,(
% 0.22/0.52    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f725])).
% 0.22/0.52  fof(f725,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.52    inference(backward_demodulation,[],[f297,f723])).
% 0.22/0.52  fof(f723,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.52    inference(backward_demodulation,[],[f154,f722])).
% 0.22/0.52  fof(f722,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f721,f140])).
% 0.22/0.52  fof(f721,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f717,f361])).
% 0.22/0.52  fof(f361,plain,(
% 0.22/0.52    sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1)),
% 0.22/0.52    inference(backward_demodulation,[],[f196,f358])).
% 0.22/0.52  fof(f358,plain,(
% 0.22/0.52    sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)),
% 0.22/0.52    inference(resolution,[],[f357,f74])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)),
% 0.22/0.52    inference(resolution,[],[f193,f74])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k12_lattice3(k2_yellow_1(sK0),X0,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f192,f74])).
% 0.22/0.52  fof(f717,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK1))),
% 0.22/0.52    inference(resolution,[],[f708,f74])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.52    inference(forward_demodulation,[],[f152,f140])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK1))),
% 0.22/0.52    inference(resolution,[],[f148,f75])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f141,f74])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0)) )),
% 0.22/0.52    inference(resolution,[],[f136,f100])).
% 0.22/0.52  fof(f297,plain,(
% 0.22/0.52    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f296,f56])).
% 0.22/0.52  fof(f296,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f295,f74])).
% 0.22/0.52  fof(f295,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,sK0) | k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.52    inference(forward_demodulation,[],[f294,f56])).
% 0.22/0.52  fof(f294,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f293,f52])).
% 0.22/0.52  fof(f293,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f292,f54])).
% 0.22/0.52  fof(f292,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f291,f48])).
% 0.22/0.52  fof(f291,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f290,f55])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.22/0.52    inference(superposition,[],[f62,f281])).
% 0.22/0.52  fof(f281,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f280,f154])).
% 0.22/0.52  fof(f280,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f277,f140])).
% 0.22/0.52  fof(f277,plain,(
% 0.22/0.52    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1)),
% 0.22/0.52    inference(resolution,[],[f273,f75])).
% 0.22/0.52  fof(f273,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK1),sK1)) )),
% 0.22/0.52    inference(resolution,[],[f198,f74])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK1) | ~m1_subset_1(X0,sK0)) )),
% 0.22/0.52    inference(resolution,[],[f193,f100])).
% 0.22/0.52  fof(f475,plain,(
% 0.22/0.52    spl3_12),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f474])).
% 0.22/0.52  fof(f474,plain,(
% 0.22/0.52    $false | spl3_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f473,f74])).
% 0.22/0.52  fof(f473,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,sK0) | spl3_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f472,f75])).
% 0.22/0.52  fof(f472,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | spl3_12),
% 0.22/0.52    inference(resolution,[],[f470,f100])).
% 0.22/0.52  fof(f470,plain,(
% 0.22/0.52    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | spl3_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f468])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ~spl3_1 | ~spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f82,f88,f84])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.52    inference(resolution,[],[f73,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.22/0.52    inference(definition_unfolding,[],[f51,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f71,f66])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (26236)------------------------------
% 0.22/0.52  % (26236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26236)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (26236)Memory used [KB]: 11129
% 0.22/0.52  % (26236)Time elapsed: 0.090 s
% 0.22/0.52  % (26236)------------------------------
% 0.22/0.52  % (26236)------------------------------
% 0.22/0.52  % (26226)Success in time 0.156 s
%------------------------------------------------------------------------------
