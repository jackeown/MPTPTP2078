%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 845 expanded)
%              Number of leaves         :   20 ( 293 expanded)
%              Depth                    :   40
%              Number of atoms          :  682 (3500 expanded)
%              Number of equality atoms :   84 ( 323 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f638,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f517,f521,f600,f637])).

fof(f637,plain,
    ( spl3_1
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | spl3_1
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f635,f38])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

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

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f635,plain,
    ( v1_xboole_0(sK0)
    | spl3_1
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f634,f507])).

fof(f507,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl3_17
  <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f634,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | spl3_1
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f633,f76])).

fof(f76,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_1
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f633,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f631,f69])).

fof(f69,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f40,f49])).

fof(f49,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f40,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f631,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_17 ),
    inference(resolution,[],[f622,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f84,f49])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f51,f49])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f622,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f621,f507])).

fof(f621,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f620,f49])).

fof(f620,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f619,f69])).

fof(f619,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f618,f49])).

fof(f618,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f617,f44])).

fof(f44,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f617,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f616,f46])).

fof(f46,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f616,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f615,f39])).

fof(f39,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f615,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f614,f48])).

fof(f48,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f614,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f613,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f613,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ spl3_17 ),
    inference(duplicate_literal_removal,[],[f610])).

fof(f610,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ spl3_17 ),
    inference(superposition,[],[f116,f563])).

fof(f563,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f539,f442])).

fof(f442,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f153,f436])).

fof(f436,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f433,f364])).

fof(f364,plain,(
    sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
    inference(backward_demodulation,[],[f217,f356])).

fof(f356,plain,(
    sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
    inference(subsumption_resolution,[],[f352,f66])).

fof(f352,plain,
    ( sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f297,f69])).

fof(f297,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,X1)
      | ~ r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f182,f69])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k12_lattice3(k2_yellow_1(sK0),X1,X0) = X1
      | ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f181,f38])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | k12_lattice3(k2_yellow_1(sK0),X1,X0) = X1
      | ~ m1_subset_1(X1,sK0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f133,f39])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f131,f49])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f129,f49])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f128,f44])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f127,f46])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f126,f48])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f54,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f88,f49])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f52,f49])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | k12_lattice3(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f217,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
    inference(resolution,[],[f159,f69])).

fof(f159,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X1,sK1) = k12_lattice3(k2_yellow_1(sK0),X1,sK1) ) ),
    inference(resolution,[],[f157,f69])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k12_lattice3(k2_yellow_1(sK0),X0,X1) ) ),
    inference(resolution,[],[f107,f39])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f106,f46])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f104,f48])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f61,f49])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f433,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(resolution,[],[f424,f69])).

fof(f424,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X1,sK2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X1),sK2) ) ),
    inference(resolution,[],[f389,f69])).

fof(f389,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X1,k11_lattice3(k2_yellow_1(sK0),X0,sK2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X1,X0),sK2) ) ),
    inference(resolution,[],[f213,f68])).

fof(f68,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f41,f49])).

fof(f41,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,k11_lattice3(k2_yellow_1(sK0),X1,X2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),X2) ) ),
    inference(resolution,[],[f148,f39])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f147,f46])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f45,plain,(
    ! [X0] : v4_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ v4_orders_2(k2_yellow_1(X0))
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f56,f49])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
                   => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_lattice3)).

fof(f153,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(resolution,[],[f149,f69])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,sK2)) ) ),
    inference(resolution,[],[f115,f68])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f100,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f82,f48])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f62,f49])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

% (25231)Refutation not found, incomplete strategy% (25231)------------------------------
% (25231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25231)Termination reason: Refutation not found, incomplete strategy

% (25231)Memory used [KB]: 1791
% (25231)Time elapsed: 0.131 s
fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

% (25231)------------------------------
% (25231)------------------------------
fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f100,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X1,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X1) ) ),
    inference(resolution,[],[f98,f69])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f97,f39])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f94,f48])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f55,f49])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

fof(f539,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_17 ),
    inference(resolution,[],[f507,f159])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k12_lattice3(X1,X0,X2),X0)
      | ~ r1_tarski(X0,k12_lattice3(X1,X0,X2))
      | r3_orders_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(extensionality_resolution,[],[f60,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) != X1
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f600,plain,
    ( spl3_2
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | spl3_2
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f598,f38])).

fof(f598,plain,
    ( v1_xboole_0(sK0)
    | spl3_2
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f597,f507])).

fof(f597,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | spl3_2
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f596,f80])).

fof(f80,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_2
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f596,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f594,f68])).

fof(f594,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | v1_xboole_0(sK0)
    | ~ spl3_16 ),
    inference(resolution,[],[f504,f85])).

fof(f504,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl3_16
  <=> r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f521,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | spl3_17 ),
    inference(subsumption_resolution,[],[f519,f69])).

fof(f519,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl3_17 ),
    inference(subsumption_resolution,[],[f518,f68])).

fof(f518,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | spl3_17 ),
    inference(resolution,[],[f508,f83])).

fof(f508,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f506])).

fof(f517,plain,
    ( spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f516,f506,f502])).

fof(f516,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f515,f49])).

fof(f515,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f514,f68])).

fof(f514,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f513,f49])).

fof(f513,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f512,f44])).

fof(f512,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f511,f46])).

fof(f511,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f510,f39])).

fof(f510,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f491,f48])).

fof(f491,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f490])).

fof(f490,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0)) ),
    inference(superposition,[],[f53,f488])).

fof(f488,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f484,f435])).

fof(f435,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f432,f305])).

fof(f305,plain,(
    sK2 = k11_lattice3(k2_yellow_1(sK0),sK2,sK2) ),
    inference(backward_demodulation,[],[f161,f302])).

fof(f302,plain,(
    sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f299,f66])).

fof(f299,plain,
    ( sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,sK2)
    | ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[],[f296,f68])).

fof(f296,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,X0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f182,f68])).

fof(f161,plain,(
    k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = k12_lattice3(k2_yellow_1(sK0),sK2,sK2) ),
    inference(resolution,[],[f158,f68])).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),X0,sK2) = k12_lattice3(k2_yellow_1(sK0),X0,sK2) ) ),
    inference(resolution,[],[f157,f68])).

fof(f432,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) ),
    inference(resolution,[],[f424,f68])).

fof(f484,plain,(
    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(resolution,[],[f479,f69])).

fof(f479,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK2),sK2) ) ),
    inference(resolution,[],[f163,f68])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f158,f83])).

fof(f81,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f71,f78,f74])).

fof(f71,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(resolution,[],[f65,f64])).

fof(f64,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f57,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (25221)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.49  % (25243)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.49  % (25243)Refutation not found, incomplete strategy% (25243)------------------------------
% 0.21/0.49  % (25243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25243)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (25243)Memory used [KB]: 10746
% 0.21/0.49  % (25243)Time elapsed: 0.072 s
% 0.21/0.49  % (25243)------------------------------
% 0.21/0.49  % (25243)------------------------------
% 0.21/0.50  % (25219)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (25236)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (25217)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (25218)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (25228)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (25228)Refutation not found, incomplete strategy% (25228)------------------------------
% 0.21/0.51  % (25228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25228)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25228)Memory used [KB]: 1663
% 0.21/0.51  % (25228)Time elapsed: 0.058 s
% 0.21/0.51  % (25228)------------------------------
% 0.21/0.51  % (25228)------------------------------
% 0.21/0.52  % (25220)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (25216)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (25241)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (25239)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (25233)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (25235)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (25237)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (25232)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (25224)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (25215)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (25226)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (25229)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (25227)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (25225)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (25213)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (25240)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (25240)Refutation not found, incomplete strategy% (25240)------------------------------
% 0.21/0.54  % (25240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25240)Memory used [KB]: 6268
% 0.21/0.54  % (25240)Time elapsed: 0.129 s
% 0.21/0.54  % (25240)------------------------------
% 0.21/0.54  % (25240)------------------------------
% 0.21/0.54  % (25231)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (25219)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f638,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f81,f517,f521,f600,f637])).
% 0.21/0.54  fof(f637,plain,(
% 0.21/0.54    spl3_1 | ~spl3_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f636])).
% 0.21/0.54  fof(f636,plain,(
% 0.21/0.54    $false | (spl3_1 | ~spl3_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f635,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32,f31,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.21/0.54  fof(f635,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | (spl3_1 | ~spl3_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f634,f507])).
% 0.21/0.54  fof(f507,plain,(
% 0.21/0.54    m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~spl3_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f506])).
% 0.21/0.54  fof(f506,plain,(
% 0.21/0.54    spl3_17 <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.54  fof(f634,plain,(
% 0.21/0.54    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | (spl3_1 | ~spl3_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f633,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    spl3_1 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f633,plain,(
% 0.21/0.54    r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | ~spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f631,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f40,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f631,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,sK0) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | ~spl3_17),
% 0.21/0.54    inference(resolution,[],[f622,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f84,f49])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f51,f49])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.54  fof(f622,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f621,f507])).
% 0.21/0.54  fof(f621,plain,(
% 0.21/0.54    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~spl3_17),
% 0.21/0.54    inference(forward_demodulation,[],[f620,f49])).
% 0.21/0.54  fof(f620,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f619,f69])).
% 0.21/0.54  fof(f619,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,sK0) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~spl3_17),
% 0.21/0.54    inference(forward_demodulation,[],[f618,f49])).
% 0.21/0.54  fof(f618,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f617,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.54  fof(f617,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v3_orders_2(k2_yellow_1(sK0)) | ~spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f616,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f616,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | ~spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f615,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    v2_lattice3(k2_yellow_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f615,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | ~spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f614,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.54  fof(f614,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | ~spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f613,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f613,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | ~spl3_17),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f610])).
% 0.21/0.54  fof(f610,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | ~spl3_17),
% 0.21/0.54    inference(superposition,[],[f116,f563])).
% 0.21/0.54  fof(f563,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~spl3_17),
% 0.21/0.54    inference(forward_demodulation,[],[f539,f442])).
% 0.21/0.54  fof(f442,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(backward_demodulation,[],[f153,f436])).
% 0.21/0.54  fof(f436,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.54    inference(forward_demodulation,[],[f433,f364])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1)),
% 0.21/0.54    inference(backward_demodulation,[],[f217,f356])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f352,f66])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) | ~r1_tarski(sK1,sK1)),
% 0.21/0.54    inference(resolution,[],[f297,f69])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,sK0) | sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,X1) | ~r1_tarski(sK1,X1)) )),
% 0.21/0.54    inference(resolution,[],[f182,f69])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k12_lattice3(k2_yellow_1(sK0),X1,X0) = X1 | ~m1_subset_1(X0,sK0) | ~r1_tarski(X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f181,f38])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | k12_lattice3(k2_yellow_1(sK0),X1,X0) = X1 | ~m1_subset_1(X1,sK0) | ~r1_tarski(X1,X0) | v1_xboole_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f133,f39])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~v2_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f131,f49])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f130])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f129,f49])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f128,f44])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f127,f46])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f126,f48])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f54,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f88,f49])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f52,f49])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)),
% 0.21/0.54    inference(resolution,[],[f159,f69])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),X1,sK1) = k12_lattice3(k2_yellow_1(sK0),X1,sK1)) )),
% 0.21/0.54    inference(resolution,[],[f157,f69])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k12_lattice3(k2_yellow_1(sK0),X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f107,f39])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X0)) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f106,f46])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f104,f48])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(superposition,[],[f61,f49])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.54  fof(f433,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.54    inference(resolution,[],[f424,f69])).
% 0.21/0.54  fof(f424,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X1,sK2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X1),sK2)) )),
% 0.21/0.54    inference(resolution,[],[f389,f69])).
% 0.21/0.54  fof(f389,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X1,k11_lattice3(k2_yellow_1(sK0),X0,sK2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X1,X0),sK2)) )),
% 0.21/0.54    inference(resolution,[],[f213,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    m1_subset_1(sK2,sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f41,f49])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,k11_lattice3(k2_yellow_1(sK0),X1,X2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),X2)) )),
% 0.21/0.54    inference(resolution,[],[f148,f39])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v2_lattice3(k2_yellow_1(X0)) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f147,f46])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f146,f48])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f144,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0] : (v4_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,X0) | ~v4_orders_2(k2_yellow_1(X0)) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X2,X3),X1) = k11_lattice3(k2_yellow_1(X0),X2,k11_lattice3(k2_yellow_1(X0),X3,X1)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(superposition,[],[f56,f49])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_orders_2(X0) | k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (v4_orders_2(X0) => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_lattice3)).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.54    inference(resolution,[],[f149,f69])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,sK2))) )),
% 0.21/0.54    inference(resolution,[],[f115,f68])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f100,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f82,f48])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(superposition,[],[f62,f49])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  % (25231)Refutation not found, incomplete strategy% (25231)------------------------------
% 0.21/0.54  % (25231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25231)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25231)Memory used [KB]: 1791
% 0.21/0.54  % (25231)Time elapsed: 0.131 s
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  % (25231)------------------------------
% 0.21/0.54  % (25231)------------------------------
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),X1,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X1)) )),
% 0.21/0.54    inference(resolution,[],[f98,f69])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f97,f39])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X0)) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f96,f46])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f94,f48])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.54    inference(superposition,[],[f55,f49])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).
% 0.21/0.54  fof(f539,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~spl3_17),
% 0.21/0.54    inference(resolution,[],[f507,f159])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k12_lattice3(X1,X0,X2),X0) | ~r1_tarski(X0,k12_lattice3(X1,X0,X2)) | r3_orders_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~v3_orders_2(X1)) )),
% 0.21/0.54    inference(extensionality_resolution,[],[f60,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f600,plain,(
% 0.21/0.54    spl3_2 | ~spl3_16 | ~spl3_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f599])).
% 0.21/0.54  fof(f599,plain,(
% 0.21/0.54    $false | (spl3_2 | ~spl3_16 | ~spl3_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f598,f38])).
% 0.21/0.54  fof(f598,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | (spl3_2 | ~spl3_16 | ~spl3_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f597,f507])).
% 0.21/0.54  fof(f597,plain,(
% 0.21/0.54    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | (spl3_2 | ~spl3_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f596,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl3_2 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f596,plain,(
% 0.21/0.54    r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | ~spl3_16),
% 0.21/0.54    inference(subsumption_resolution,[],[f594,f68])).
% 0.21/0.54  fof(f594,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,sK0) | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | v1_xboole_0(sK0) | ~spl3_16),
% 0.21/0.54    inference(resolution,[],[f504,f85])).
% 0.21/0.54  fof(f504,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~spl3_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f502])).
% 0.21/0.54  fof(f502,plain,(
% 0.21/0.54    spl3_16 <=> r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.54  fof(f521,plain,(
% 0.21/0.54    spl3_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f520])).
% 0.21/0.54  fof(f520,plain,(
% 0.21/0.54    $false | spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f519,f69])).
% 0.21/0.54  fof(f519,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,sK0) | spl3_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f518,f68])).
% 0.21/0.54  fof(f518,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | spl3_17),
% 0.21/0.54    inference(resolution,[],[f508,f83])).
% 0.21/0.54  fof(f508,plain,(
% 0.21/0.54    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | spl3_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f506])).
% 0.21/0.54  fof(f517,plain,(
% 0.21/0.54    spl3_16 | ~spl3_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f516,f506,f502])).
% 0.21/0.54  fof(f516,plain,(
% 0.21/0.54    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.54    inference(forward_demodulation,[],[f515,f49])).
% 0.21/0.54  fof(f515,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f514,f68])).
% 0.21/0.54  fof(f514,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,sK0) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.54    inference(forward_demodulation,[],[f513,f49])).
% 0.21/0.54  fof(f513,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f512,f44])).
% 0.21/0.54  fof(f512,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f511,f46])).
% 0.21/0.54  fof(f511,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f510,f39])).
% 0.21/0.54  fof(f510,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f491,f48])).
% 0.21/0.54  fof(f491,plain,(
% 0.21/0.54    r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f490])).
% 0.21/0.54  fof(f490,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2) | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0))),
% 0.21/0.54    inference(superposition,[],[f53,f488])).
% 0.21/0.54  fof(f488,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.54    inference(forward_demodulation,[],[f484,f435])).
% 0.21/0.54  fof(f435,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.54    inference(forward_demodulation,[],[f432,f305])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    sK2 = k11_lattice3(k2_yellow_1(sK0),sK2,sK2)),
% 0.21/0.54    inference(backward_demodulation,[],[f161,f302])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f299,f66])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,sK2) | ~r1_tarski(sK2,sK2)),
% 0.21/0.54    inference(resolution,[],[f296,f68])).
% 0.21/0.54  fof(f296,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,sK0) | sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,X0) | ~r1_tarski(sK2,X0)) )),
% 0.21/0.54    inference(resolution,[],[f182,f68])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = k12_lattice3(k2_yellow_1(sK0),sK2,sK2)),
% 0.21/0.54    inference(resolution,[],[f158,f68])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),X0,sK2) = k12_lattice3(k2_yellow_1(sK0),X0,sK2)) )),
% 0.21/0.54    inference(resolution,[],[f157,f68])).
% 0.21/0.54  fof(f432,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2))),
% 0.21/0.54    inference(resolution,[],[f424,f68])).
% 0.21/0.54  fof(f484,plain,(
% 0.21/0.54    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.21/0.54    inference(resolution,[],[f479,f69])).
% 0.21/0.54  fof(f479,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,sK2),sK2)) )),
% 0.21/0.54    inference(resolution,[],[f163,f68])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),X0,X1),sK2) | ~m1_subset_1(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f158,f83])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ~spl3_1 | ~spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f71,f78,f74])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.54    inference(resolution,[],[f65,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.21/0.54    inference(definition_unfolding,[],[f42,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f63,f57])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (25219)------------------------------
% 0.21/0.54  % (25219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25219)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (25219)Memory used [KB]: 11001
% 0.21/0.54  % (25219)Time elapsed: 0.095 s
% 0.21/0.54  % (25219)------------------------------
% 0.21/0.54  % (25219)------------------------------
% 0.21/0.54  % (25241)Refutation not found, incomplete strategy% (25241)------------------------------
% 0.21/0.54  % (25241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25241)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25241)Memory used [KB]: 6268
% 0.21/0.54  % (25241)Time elapsed: 0.115 s
% 0.21/0.54  % (25241)------------------------------
% 0.21/0.54  % (25241)------------------------------
% 0.21/0.54  % (25209)Success in time 0.179 s
%------------------------------------------------------------------------------
