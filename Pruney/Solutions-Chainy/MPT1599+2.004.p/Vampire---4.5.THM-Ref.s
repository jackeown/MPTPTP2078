%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:29 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  232 ( 925 expanded)
%              Number of leaves         :   30 ( 314 expanded)
%              Depth                    :   31
%              Number of atoms          : 1038 (4246 expanded)
%              Number of equality atoms :   88 ( 320 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1721,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f159,f221,f666,f746,f758,f1080,f1639,f1720])).

fof(f1720,plain,
    ( spl6_1
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1719])).

fof(f1719,plain,
    ( $false
    | spl6_1
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1718,f53])).

fof(f53,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))
    & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    & v2_lattice3(k2_yellow_1(sK2))
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f40,f39,f38])).

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
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) )
      & v2_lattice3(k2_yellow_1(sK2))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
      & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))
      & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f1718,plain,
    ( v1_xboole_0(sK2)
    | spl6_1
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1717,f634])).

fof(f634,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl6_24
  <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f1717,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | spl6_1
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1716,f106])).

fof(f106,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_1
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1716,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1714,f99])).

fof(f99,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f55,f64])).

fof(f64,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f55,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f1714,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(resolution,[],[f1697,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f114,f64])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f66,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

% (444)Refutation not found, incomplete strategy% (444)------------------------------
% (444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (444)Termination reason: Refutation not found, incomplete strategy

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

% (444)Memory used [KB]: 10746
% (444)Time elapsed: 0.102 s
% (444)------------------------------
% (444)------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f1697,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1696,f634])).

fof(f1696,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f1695,f64])).

fof(f1695,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1694,f99])).

fof(f1694,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f1693,f64])).

fof(f1693,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1692,f59])).

fof(f59,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f1692,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1691,f61])).

fof(f61,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1691,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1690,f54])).

fof(f54,plain,(
    v2_lattice3(k2_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f1690,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1689,f63])).

fof(f63,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f1689,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1688,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f1688,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(duplicate_literal_removal,[],[f1685])).

fof(f1685,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(superposition,[],[f226,f1610])).

fof(f1610,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f1605,f1130])).

fof(f1130,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f668,f745])).

fof(f745,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f743])).

fof(f743,plain,
    ( spl6_28
  <=> k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f668,plain,
    ( k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_24 ),
    inference(resolution,[],[f634,f144])).

fof(f144,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK2)
      | k11_lattice3(k2_yellow_1(sK2),X1,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X1) ) ),
    inference(subsumption_resolution,[],[f139,f54])).

fof(f139,plain,(
    ! [X1] :
      ( k11_lattice3(k2_yellow_1(sK2),X1,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X1)
      | ~ m1_subset_1(X1,sK2)
      | ~ v2_lattice3(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f137,f99])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f136,f61])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f134,f63])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f81,f64])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f1605,plain,
    ( k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24 ),
    inference(resolution,[],[f681,f99])).

fof(f681,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2)
        | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) )
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f676,f54])).

fof(f676,plain,
    ( ! [X2] :
        ( k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2)
        | ~ m1_subset_1(X2,sK2)
        | ~ v2_lattice3(k2_yellow_1(sK2)) )
    | ~ spl6_24 ),
    inference(resolution,[],[f634,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f165,f61])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f163,f63])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f88,f64])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

% (445)Refutation not found, incomplete strategy% (445)------------------------------
% (445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f226,plain,(
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
    inference(extensionality_resolution,[],[f86,f79])).

% (445)Termination reason: Refutation not found, incomplete strategy

% (445)Memory used [KB]: 10746
% (445)Time elapsed: 0.101 s
% (445)------------------------------
% (445)------------------------------
fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) != X1
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1639,plain,
    ( spl6_2
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f1638])).

fof(f1638,plain,
    ( $false
    | spl6_2
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1637,f53])).

fof(f1637,plain,
    ( v1_xboole_0(sK2)
    | spl6_2
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1636,f634])).

fof(f1636,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | spl6_2
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1635,f110])).

fof(f110,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_2
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1635,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1633,f98])).

fof(f98,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(backward_demodulation,[],[f56,f64])).

fof(f56,plain,(
    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f1633,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(resolution,[],[f1624,f115])).

fof(f1624,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1623,f634])).

fof(f1623,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f1622,f64])).

fof(f1622,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1621,f98])).

fof(f1621,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f1620,f64])).

fof(f1620,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1619,f59])).

fof(f1619,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1618,f61])).

fof(f1618,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1617,f54])).

fof(f1617,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1616,f63])).

fof(f1616,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1615,f96])).

fof(f1615,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(duplicate_literal_removal,[],[f1612])).

fof(f1612,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(superposition,[],[f226,f1609])).

fof(f1609,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f1604,f1204])).

fof(f1204,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_29 ),
    inference(backward_demodulation,[],[f175,f757])).

fof(f757,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f755])).

fof(f755,plain,
    ( spl6_29
  <=> k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f175,plain,(
    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    inference(resolution,[],[f170,f99])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),X0,sK4),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),X0,sK4)) ) ),
    inference(resolution,[],[f147,f98])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK2)
      | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),X0,X1),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),X0,X1))
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(resolution,[],[f143,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f112,f63])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f89,f64])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | k11_lattice3(k2_yellow_1(sK2),X0,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,X0) ) ),
    inference(subsumption_resolution,[],[f138,f54])).

fof(f138,plain,(
    ! [X0] :
      ( k11_lattice3(k2_yellow_1(sK2),X0,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,X0)
      | ~ m1_subset_1(X0,sK2)
      | ~ v2_lattice3(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f137,f98])).

fof(f1604,plain,
    ( k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_24 ),
    inference(resolution,[],[f681,f98])).

fof(f1080,plain,
    ( ~ spl6_3
    | ~ spl6_24
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f1079])).

fof(f1079,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_24
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1078,f99])).

fof(f1078,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | ~ spl6_3
    | ~ spl6_24
    | spl6_27 ),
    inference(forward_demodulation,[],[f1077,f64])).

fof(f1077,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | ~ spl6_24
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1076,f634])).

fof(f1076,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(forward_demodulation,[],[f1075,f64])).

fof(f1075,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1074,f98])).

fof(f1074,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(forward_demodulation,[],[f1073,f64])).

fof(f1073,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1072,f223])).

fof(f223,plain,
    ( r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f154,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ~ r1_orders_2(X1,sK5(X0,X1,X2,X3),X0)
          & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2)
          & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3)
          & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) )
        | ~ r1_orders_2(X1,X0,X2)
        | ~ r1_orders_2(X1,X0,X3) )
      & ( ( ! [X5] :
              ( r1_orders_2(X1,X5,X0)
              | ~ r1_orders_2(X1,X5,X2)
              | ~ r1_orders_2(X1,X5,X3)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_orders_2(X1,X0,X2)
          & r1_orders_2(X1,X0,X3) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X4,X0)
          & r1_orders_2(X1,X4,X2)
          & r1_orders_2(X1,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK5(X0,X1,X2,X3),X0)
        & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2)
        & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3)
        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ~ r1_orders_2(X1,X4,X0)
            & r1_orders_2(X1,X4,X2)
            & r1_orders_2(X1,X4,X3)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ r1_orders_2(X1,X0,X2)
        | ~ r1_orders_2(X1,X0,X3) )
      & ( ( ! [X5] :
              ( r1_orders_2(X1,X5,X0)
              | ~ r1_orders_2(X1,X5,X2)
              | ~ r1_orders_2(X1,X5,X3)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_orders_2(X1,X0,X2)
          & r1_orders_2(X1,X0,X3) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP0(X3,X0,X2,X1)
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
        | ~ sP0(X3,X0,X2,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP0(X3,X0,X2,X1)
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
        | ~ sP0(X3,X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X3,X0,X2,X1] :
      ( sP0(X3,X0,X2,X1)
    <=> ( ! [X4] :
            ( r1_orders_2(X0,X4,X3)
            | ~ r1_orders_2(X0,X4,X2)
            | ~ r1_orders_2(X0,X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r1_orders_2(X0,X3,X2)
        & r1_orders_2(X0,X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f154,plain,
    ( sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl6_3
  <=> sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1072,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1071,f224])).

fof(f224,plain,
    ( r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_3 ),
    inference(resolution,[],[f154,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1071,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1070,f61])).

fof(f1070,plain,
    ( ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1069,f54])).

fof(f1069,plain,
    ( ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1050,f63])).

fof(f1050,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_27 ),
    inference(resolution,[],[f378,f741])).

fof(f741,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f739])).

fof(f739,plain,
    ( spl6_27
  <=> r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f378,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,k11_lattice3(X1,X0,X2))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X3,X2)
      | ~ r1_orders_2(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f193,f73])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ r1_orders_2(X1,X5,X2)
      | ~ r1_orders_2(X1,X5,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | r1_orders_2(X1,X5,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f193,plain,(
    ! [X6,X4,X5] :
      ( sP0(k11_lattice3(X4,X5,X6),X4,X6,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f190,f89])).

fof(f190,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(k11_lattice3(X4,X5,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | sP0(k11_lattice3(X4,X5,X6),X4,X6,X5) ) ),
    inference(resolution,[],[f173,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2,k11_lattice3(X2,X0,X1))
      | sP0(k11_lattice3(X2,X0,X1),X2,X1,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k11_lattice3(X2,X0,X1) != X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k11_lattice3(X2,X0,X1) = X3
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k11_lattice3(X2,X0,X1) != X3 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X0,X3] :
      ( ( ( k11_lattice3(X0,X1,X2) = X3
          | ~ sP0(X3,X0,X2,X1) )
        & ( sP0(X3,X0,X2,X1)
          | k11_lattice3(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X2,X0,X3) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X2,X0,X3] :
      ( ( k11_lattice3(X0,X1,X2) = X3
      <=> sP0(X3,X0,X2,X1) )
      | ~ sP1(X1,X2,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X1,X2,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f78,f68])).

fof(f68,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X1,X2,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X1,X2,X0,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f24,f36,f35])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

fof(f758,plain,
    ( ~ spl6_27
    | spl6_29
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f753,f633,f152,f755,f739])).

fof(f753,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f752,f634])).

fof(f752,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f751,f64])).

fof(f751,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f750,f98])).

fof(f750,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f749,f64])).

fof(f749,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f748,f61])).

fof(f748,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f747,f54])).

fof(f747,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f719,f63])).

fof(f719,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(resolution,[],[f449,f224])).

fof(f449,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k11_lattice3(X1,X2,X0) = X0
      | ~ r1_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k11_lattice3(X1,X2,X0) = X0
      | ~ r1_orders_2(X1,X0,X0)
      | ~ r1_orders_2(X1,X0,X2) ) ),
    inference(resolution,[],[f189,f123])).

fof(f123,plain,(
    ! [X4,X5,X3] :
      ( sP0(X3,X4,X3,X5)
      | ~ r1_orders_2(X4,X3,X3)
      | ~ r1_orders_2(X4,X3,X5) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X4,X5,X3] :
      ( sP0(X3,X4,X3,X5)
      | ~ r1_orders_2(X4,X3,X3)
      | ~ r1_orders_2(X4,X3,X5)
      | sP0(X3,X4,X3,X5)
      | ~ r1_orders_2(X4,X3,X3)
      | ~ r1_orders_2(X4,X3,X5) ) ),
    inference(resolution,[],[f77,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK5(X0,X1,X2,X3),X2)
      | sP0(X0,X1,X2,X3)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2,X3),X0)
      | sP0(X0,X1,X2,X3)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f189,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k11_lattice3(X1,X3,X2) = X0 ) ),
    inference(resolution,[],[f173,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X3,X2,X1,X0)
      | k11_lattice3(X2,X0,X1) = X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f746,plain,
    ( ~ spl6_27
    | spl6_28
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f737,f633,f152,f743,f739])).

fof(f737,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f736,f634])).

fof(f736,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f735,f64])).

fof(f735,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f734,f99])).

fof(f734,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f733,f64])).

fof(f733,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f732,f61])).

fof(f732,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f731,f54])).

fof(f731,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f718,f63])).

fof(f718,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(resolution,[],[f449,f223])).

fof(f666,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | spl6_24 ),
    inference(subsumption_resolution,[],[f664,f99])).

fof(f664,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | spl6_24 ),
    inference(subsumption_resolution,[],[f663,f98])).

fof(f663,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(sK3,sK2)
    | spl6_24 ),
    inference(resolution,[],[f635,f113])).

fof(f635,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f633])).

fof(f221,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f219,f99])).

fof(f219,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f218,f98])).

fof(f218,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(sK3,sK2)
    | spl6_4 ),
    inference(resolution,[],[f201,f113])).

fof(f201,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f200,f98])).

fof(f200,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | spl6_4 ),
    inference(forward_demodulation,[],[f199,f64])).

fof(f199,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f198,f99])).

fof(f198,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_4 ),
    inference(forward_demodulation,[],[f197,f64])).

fof(f197,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_4 ),
    inference(forward_demodulation,[],[f196,f64])).

fof(f196,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f195,f61])).

fof(f195,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f194,f54])).

fof(f194,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f191,f63])).

fof(f191,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | spl6_4 ),
    inference(resolution,[],[f173,f158])).

fof(f158,plain,
    ( ~ sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_4
  <=> sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f159,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f150,f156,f152])).

fof(f150,plain,
    ( ~ sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4) ),
    inference(superposition,[],[f95,f146])).

fof(f146,plain,(
    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,sK3) ),
    inference(resolution,[],[f143,f99])).

fof(f111,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f102,f108,f104])).

fof(f102,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) ),
    inference(resolution,[],[f94,f93])).

fof(f93,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(definition_unfolding,[],[f57,f92])).

fof(f92,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f82,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f83,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f83,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f82,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f90,f92])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (421)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.47  % (421)Refutation not found, incomplete strategy% (421)------------------------------
% 0.21/0.47  % (421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (421)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (421)Memory used [KB]: 10746
% 0.21/0.47  % (421)Time elapsed: 0.066 s
% 0.21/0.47  % (421)------------------------------
% 0.21/0.47  % (421)------------------------------
% 0.21/0.48  % (431)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (415)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (414)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.53  % (433)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.54  % (411)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.23/0.54  % (412)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.54  % (416)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.54  % (412)Refutation not found, incomplete strategy% (412)------------------------------
% 1.23/0.54  % (412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (412)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (412)Memory used [KB]: 1663
% 1.23/0.54  % (412)Time elapsed: 0.122 s
% 1.23/0.54  % (412)------------------------------
% 1.23/0.54  % (412)------------------------------
% 1.23/0.54  % (438)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.23/0.54  % (436)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.23/0.54  % (424)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.23/0.54  % (436)Refutation not found, incomplete strategy% (436)------------------------------
% 1.23/0.54  % (436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (436)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (436)Memory used [KB]: 6268
% 1.23/0.54  % (436)Time elapsed: 0.140 s
% 1.23/0.54  % (436)------------------------------
% 1.23/0.54  % (436)------------------------------
% 1.23/0.54  % (422)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.54  % (422)Refutation not found, incomplete strategy% (422)------------------------------
% 1.23/0.54  % (422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (422)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (422)Memory used [KB]: 6268
% 1.23/0.54  % (422)Time elapsed: 0.137 s
% 1.23/0.54  % (422)------------------------------
% 1.23/0.54  % (422)------------------------------
% 1.23/0.54  % (427)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.23/0.54  % (429)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.23/0.54  % (425)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.55  % (425)Refutation not found, incomplete strategy% (425)------------------------------
% 1.23/0.55  % (425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.55  % (425)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.55  
% 1.23/0.55  % (425)Memory used [KB]: 1791
% 1.23/0.55  % (425)Time elapsed: 0.112 s
% 1.23/0.55  % (425)------------------------------
% 1.23/0.55  % (425)------------------------------
% 1.23/0.55  % (418)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.49/0.55  % (427)Refutation not found, incomplete strategy% (427)------------------------------
% 1.49/0.55  % (427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (427)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (427)Memory used [KB]: 10746
% 1.49/0.55  % (427)Time elapsed: 0.138 s
% 1.49/0.55  % (427)------------------------------
% 1.49/0.55  % (427)------------------------------
% 1.49/0.55  % (413)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.49/0.55  % (417)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.55  % (423)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.55  % (419)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.49/0.55  % (426)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.49/0.55  % (440)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.49/0.55  % (437)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.49/0.55  % (440)Refutation not found, incomplete strategy% (440)------------------------------
% 1.49/0.55  % (440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (440)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (440)Memory used [KB]: 1663
% 1.49/0.55  % (440)Time elapsed: 0.144 s
% 1.49/0.55  % (440)------------------------------
% 1.49/0.55  % (440)------------------------------
% 1.49/0.55  % (420)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.49/0.55  % (437)Refutation not found, incomplete strategy% (437)------------------------------
% 1.49/0.55  % (437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (437)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (437)Memory used [KB]: 6268
% 1.49/0.55  % (437)Time elapsed: 0.148 s
% 1.49/0.55  % (437)------------------------------
% 1.49/0.55  % (437)------------------------------
% 1.49/0.55  % (432)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.56  % (430)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.49/0.56  % (434)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.49/0.56  % (435)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.49/0.56  % (428)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.56  % (428)Refutation not found, incomplete strategy% (428)------------------------------
% 1.49/0.56  % (428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (428)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (428)Memory used [KB]: 1791
% 1.49/0.56  % (428)Time elapsed: 0.158 s
% 1.49/0.56  % (428)------------------------------
% 1.49/0.56  % (428)------------------------------
% 1.49/0.56  % (438)Refutation not found, incomplete strategy% (438)------------------------------
% 1.49/0.56  % (438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (438)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (438)Memory used [KB]: 6268
% 1.49/0.56  % (438)Time elapsed: 0.115 s
% 1.49/0.56  % (438)------------------------------
% 1.49/0.56  % (438)------------------------------
% 1.49/0.57  % (439)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.49/0.58  % (439)Refutation not found, incomplete strategy% (439)------------------------------
% 1.49/0.58  % (439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (439)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (439)Memory used [KB]: 10746
% 1.49/0.58  % (439)Time elapsed: 0.165 s
% 1.49/0.58  % (439)------------------------------
% 1.49/0.58  % (439)------------------------------
% 1.49/0.60  % (441)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.01/0.64  % (414)Refutation not found, incomplete strategy% (414)------------------------------
% 2.01/0.64  % (414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.64  % (414)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.64  
% 2.01/0.64  % (414)Memory used [KB]: 6140
% 2.01/0.64  % (414)Time elapsed: 0.214 s
% 2.01/0.64  % (414)------------------------------
% 2.01/0.64  % (414)------------------------------
% 2.01/0.67  % (442)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.01/0.68  % (444)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.01/0.68  % (445)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.01/0.68  % (417)Refutation found. Thanks to Tanya!
% 2.01/0.68  % SZS status Theorem for theBenchmark
% 2.01/0.68  % SZS output start Proof for theBenchmark
% 2.01/0.68  fof(f1721,plain,(
% 2.01/0.68    $false),
% 2.01/0.68    inference(avatar_sat_refutation,[],[f111,f159,f221,f666,f746,f758,f1080,f1639,f1720])).
% 2.01/0.68  fof(f1720,plain,(
% 2.01/0.68    spl6_1 | ~spl6_24 | ~spl6_28),
% 2.01/0.68    inference(avatar_contradiction_clause,[],[f1719])).
% 2.01/0.68  fof(f1719,plain,(
% 2.01/0.68    $false | (spl6_1 | ~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1718,f53])).
% 2.01/0.68  fof(f53,plain,(
% 2.01/0.68    ~v1_xboole_0(sK2)),
% 2.01/0.68    inference(cnf_transformation,[],[f41])).
% 2.01/0.68  fof(f41,plain,(
% 2.01/0.68    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))) & v2_lattice3(k2_yellow_1(sK2)) & ~v1_xboole_0(sK2)),
% 2.01/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f40,f39,f38])).
% 2.01/0.68  fof(f38,plain,(
% 2.01/0.68    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))) & v2_lattice3(k2_yellow_1(sK2)) & ~v1_xboole_0(sK2))),
% 2.01/0.68    introduced(choice_axiom,[])).
% 2.01/0.68  fof(f39,plain,(
% 2.01/0.68    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))))),
% 2.01/0.68    introduced(choice_axiom,[])).
% 2.01/0.68  fof(f40,plain,(
% 2.01/0.68    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))))),
% 2.01/0.68    introduced(choice_axiom,[])).
% 2.01/0.68  fof(f19,plain,(
% 2.01/0.68    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 2.01/0.68    inference(flattening,[],[f18])).
% 2.01/0.68  fof(f18,plain,(
% 2.01/0.68    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 2.01/0.68    inference(ennf_transformation,[],[f17])).
% 2.01/0.68  fof(f17,negated_conjecture,(
% 2.01/0.68    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.01/0.68    inference(negated_conjecture,[],[f16])).
% 2.01/0.68  fof(f16,conjecture,(
% 2.01/0.68    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).
% 2.01/0.68  fof(f1718,plain,(
% 2.01/0.68    v1_xboole_0(sK2) | (spl6_1 | ~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1717,f634])).
% 2.01/0.68  fof(f634,plain,(
% 2.01/0.68    m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~spl6_24),
% 2.01/0.68    inference(avatar_component_clause,[],[f633])).
% 2.01/0.68  fof(f633,plain,(
% 2.01/0.68    spl6_24 <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)),
% 2.01/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.01/0.68  fof(f1717,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (spl6_1 | ~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1716,f106])).
% 2.01/0.68  fof(f106,plain,(
% 2.01/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | spl6_1),
% 2.01/0.68    inference(avatar_component_clause,[],[f104])).
% 2.01/0.68  fof(f104,plain,(
% 2.01/0.68    spl6_1 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)),
% 2.01/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.01/0.68  fof(f1716,plain,(
% 2.01/0.68    r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1714,f99])).
% 2.01/0.68  fof(f99,plain,(
% 2.01/0.68    m1_subset_1(sK3,sK2)),
% 2.01/0.68    inference(backward_demodulation,[],[f55,f64])).
% 2.01/0.68  fof(f64,plain,(
% 2.01/0.68    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.01/0.68    inference(cnf_transformation,[],[f14])).
% 2.01/0.68  fof(f14,axiom,(
% 2.01/0.68    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 2.01/0.68  fof(f55,plain,(
% 2.01/0.68    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))),
% 2.01/0.68    inference(cnf_transformation,[],[f41])).
% 2.01/0.68  fof(f1714,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,sK2) | r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(resolution,[],[f1697,f115])).
% 2.01/0.68  fof(f115,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.01/0.68    inference(forward_demodulation,[],[f114,f64])).
% 2.01/0.68  fof(f114,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.01/0.68    inference(forward_demodulation,[],[f66,f64])).
% 2.01/0.68  fof(f66,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f42])).
% 2.01/0.68  fof(f42,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.01/0.68    inference(nnf_transformation,[],[f20])).
% 2.01/0.68  % (444)Refutation not found, incomplete strategy% (444)------------------------------
% 2.01/0.68  % (444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (444)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  fof(f20,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.01/0.68    inference(ennf_transformation,[],[f15])).
% 2.01/0.68  % (444)Memory used [KB]: 10746
% 2.01/0.68  % (444)Time elapsed: 0.102 s
% 2.01/0.68  % (444)------------------------------
% 2.01/0.68  % (444)------------------------------
% 2.01/0.68  fof(f15,axiom,(
% 2.01/0.68    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 2.01/0.68  fof(f1697,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1696,f634])).
% 2.01/0.68  fof(f1696,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(forward_demodulation,[],[f1695,f64])).
% 2.01/0.68  fof(f1695,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1694,f99])).
% 2.01/0.68  fof(f1694,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,sK2) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(forward_demodulation,[],[f1693,f64])).
% 2.01/0.68  fof(f1693,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1692,f59])).
% 2.01/0.68  fof(f59,plain,(
% 2.01/0.68    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(cnf_transformation,[],[f13])).
% 2.01/0.68  fof(f13,axiom,(
% 2.01/0.68    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 2.01/0.68  fof(f1692,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1691,f61])).
% 2.01/0.68  fof(f61,plain,(
% 2.01/0.68    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(cnf_transformation,[],[f13])).
% 2.01/0.68  fof(f1691,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1690,f54])).
% 2.01/0.68  fof(f54,plain,(
% 2.01/0.68    v2_lattice3(k2_yellow_1(sK2))),
% 2.01/0.68    inference(cnf_transformation,[],[f41])).
% 2.01/0.68  fof(f1690,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1689,f63])).
% 2.01/0.68  fof(f63,plain,(
% 2.01/0.68    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(cnf_transformation,[],[f12])).
% 2.01/0.68  fof(f12,axiom,(
% 2.01/0.68    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 2.01/0.68  fof(f1689,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1688,f96])).
% 2.01/0.68  fof(f96,plain,(
% 2.01/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.01/0.68    inference(equality_resolution,[],[f85])).
% 2.01/0.68  fof(f85,plain,(
% 2.01/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.01/0.68    inference(cnf_transformation,[],[f52])).
% 2.01/0.68  fof(f52,plain,(
% 2.01/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.68    inference(flattening,[],[f51])).
% 2.01/0.68  fof(f51,plain,(
% 2.01/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.68    inference(nnf_transformation,[],[f1])).
% 2.01/0.68  fof(f1,axiom,(
% 2.01/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.01/0.68  fof(f1688,plain,(
% 2.01/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(duplicate_literal_removal,[],[f1685])).
% 2.01/0.68  fof(f1685,plain,(
% 2.01/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(superposition,[],[f226,f1610])).
% 2.01/0.68  fof(f1610,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(forward_demodulation,[],[f1605,f1130])).
% 2.01/0.68  fof(f1130,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | (~spl6_24 | ~spl6_28)),
% 2.01/0.68    inference(backward_demodulation,[],[f668,f745])).
% 2.01/0.68  fof(f745,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_28),
% 2.01/0.68    inference(avatar_component_clause,[],[f743])).
% 2.01/0.68  fof(f743,plain,(
% 2.01/0.68    spl6_28 <=> k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.01/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.01/0.68  fof(f668,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_24),
% 2.01/0.68    inference(resolution,[],[f634,f144])).
% 2.01/0.68  fof(f144,plain,(
% 2.01/0.68    ( ! [X1] : (~m1_subset_1(X1,sK2) | k11_lattice3(k2_yellow_1(sK2),X1,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X1)) )),
% 2.01/0.68    inference(subsumption_resolution,[],[f139,f54])).
% 2.01/0.68  fof(f139,plain,(
% 2.01/0.68    ( ! [X1] : (k11_lattice3(k2_yellow_1(sK2),X1,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X1) | ~m1_subset_1(X1,sK2) | ~v2_lattice3(k2_yellow_1(sK2))) )),
% 2.01/0.68    inference(resolution,[],[f137,f99])).
% 2.01/0.68  fof(f137,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(subsumption_resolution,[],[f136,f61])).
% 2.01/0.68  fof(f136,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(subsumption_resolution,[],[f134,f63])).
% 2.01/0.68  fof(f134,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(superposition,[],[f81,f64])).
% 2.01/0.68  fof(f81,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f28])).
% 2.01/0.68  fof(f28,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.01/0.68    inference(flattening,[],[f27])).
% 2.01/0.68  fof(f27,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.01/0.68    inference(ennf_transformation,[],[f10])).
% 2.01/0.68  fof(f10,axiom,(
% 2.01/0.68    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).
% 2.01/0.68  fof(f1605,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~spl6_24),
% 2.01/0.68    inference(resolution,[],[f681,f99])).
% 2.01/0.68  fof(f681,plain,(
% 2.01/0.68    ( ! [X2] : (~m1_subset_1(X2,sK2) | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2)) ) | ~spl6_24),
% 2.01/0.68    inference(subsumption_resolution,[],[f676,f54])).
% 2.01/0.68  fof(f676,plain,(
% 2.01/0.68    ( ! [X2] : (k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) | ~m1_subset_1(X2,sK2) | ~v2_lattice3(k2_yellow_1(sK2))) ) | ~spl6_24),
% 2.01/0.68    inference(resolution,[],[f634,f166])).
% 2.01/0.68  fof(f166,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(subsumption_resolution,[],[f165,f61])).
% 2.01/0.68  fof(f165,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(subsumption_resolution,[],[f163,f63])).
% 2.01/0.68  fof(f163,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(superposition,[],[f88,f64])).
% 2.01/0.68  fof(f88,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f30])).
% 2.01/0.68  fof(f30,plain,(
% 2.01/0.68    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.01/0.68    inference(flattening,[],[f29])).
% 2.01/0.68  fof(f29,plain,(
% 2.01/0.68    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.01/0.68    inference(ennf_transformation,[],[f9])).
% 2.01/0.68  fof(f9,axiom,(
% 2.01/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 2.01/0.68  % (445)Refutation not found, incomplete strategy% (445)------------------------------
% 2.01/0.68  % (445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  fof(f226,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~r1_tarski(k12_lattice3(X1,X0,X2),X0) | ~r1_tarski(X0,k12_lattice3(X1,X0,X2)) | r3_orders_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~v3_orders_2(X1)) )),
% 2.01/0.68    inference(extensionality_resolution,[],[f86,f79])).
% 2.01/0.68  % (445)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  % (445)Memory used [KB]: 10746
% 2.01/0.68  % (445)Time elapsed: 0.101 s
% 2.01/0.68  % (445)------------------------------
% 2.01/0.68  % (445)------------------------------
% 2.01/0.68  fof(f79,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f50])).
% 2.01/0.68  fof(f50,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 2.01/0.68    inference(nnf_transformation,[],[f26])).
% 2.01/0.68  fof(f26,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 2.01/0.68    inference(flattening,[],[f25])).
% 2.01/0.68  fof(f25,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 2.01/0.68    inference(ennf_transformation,[],[f11])).
% 2.01/0.68  fof(f11,axiom,(
% 2.01/0.68    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).
% 2.01/0.68  fof(f86,plain,(
% 2.01/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f52])).
% 2.01/0.68  fof(f1639,plain,(
% 2.01/0.68    spl6_2 | ~spl6_24 | ~spl6_29),
% 2.01/0.68    inference(avatar_contradiction_clause,[],[f1638])).
% 2.01/0.68  fof(f1638,plain,(
% 2.01/0.68    $false | (spl6_2 | ~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1637,f53])).
% 2.01/0.68  fof(f1637,plain,(
% 2.01/0.68    v1_xboole_0(sK2) | (spl6_2 | ~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1636,f634])).
% 2.01/0.68  fof(f1636,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (spl6_2 | ~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1635,f110])).
% 2.01/0.68  fof(f110,plain,(
% 2.01/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | spl6_2),
% 2.01/0.68    inference(avatar_component_clause,[],[f108])).
% 2.01/0.68  fof(f108,plain,(
% 2.01/0.68    spl6_2 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)),
% 2.01/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.01/0.68  fof(f1635,plain,(
% 2.01/0.68    r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1633,f98])).
% 2.01/0.68  fof(f98,plain,(
% 2.01/0.68    m1_subset_1(sK4,sK2)),
% 2.01/0.68    inference(backward_demodulation,[],[f56,f64])).
% 2.01/0.68  fof(f56,plain,(
% 2.01/0.68    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))),
% 2.01/0.68    inference(cnf_transformation,[],[f41])).
% 2.01/0.68  fof(f1633,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,sK2) | r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(resolution,[],[f1624,f115])).
% 2.01/0.68  fof(f1624,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1623,f634])).
% 2.01/0.68  fof(f1623,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(forward_demodulation,[],[f1622,f64])).
% 2.01/0.68  fof(f1622,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1621,f98])).
% 2.01/0.68  fof(f1621,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,sK2) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(forward_demodulation,[],[f1620,f64])).
% 2.01/0.68  fof(f1620,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1619,f59])).
% 2.01/0.68  fof(f1619,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1618,f61])).
% 2.01/0.68  fof(f1618,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1617,f54])).
% 2.01/0.68  fof(f1617,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1616,f63])).
% 2.01/0.68  fof(f1616,plain,(
% 2.01/0.68    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1615,f96])).
% 2.01/0.68  fof(f1615,plain,(
% 2.01/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(duplicate_literal_removal,[],[f1612])).
% 2.01/0.68  fof(f1612,plain,(
% 2.01/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(superposition,[],[f226,f1609])).
% 2.01/0.68  fof(f1609,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | (~spl6_24 | ~spl6_29)),
% 2.01/0.68    inference(forward_demodulation,[],[f1604,f1204])).
% 2.01/0.68  fof(f1204,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~spl6_29),
% 2.01/0.68    inference(backward_demodulation,[],[f175,f757])).
% 2.01/0.68  fof(f757,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_29),
% 2.01/0.68    inference(avatar_component_clause,[],[f755])).
% 2.01/0.68  fof(f755,plain,(
% 2.01/0.68    spl6_29 <=> k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.01/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.01/0.68  fof(f175,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.01/0.68    inference(resolution,[],[f170,f99])).
% 2.01/0.68  fof(f170,plain,(
% 2.01/0.68    ( ! [X0] : (~m1_subset_1(X0,sK2) | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),X0,sK4),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),X0,sK4))) )),
% 2.01/0.68    inference(resolution,[],[f147,f98])).
% 2.01/0.68  fof(f147,plain,(
% 2.01/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,sK2) | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),X0,X1),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),X0,X1)) | ~m1_subset_1(X0,sK2)) )),
% 2.01/0.68    inference(resolution,[],[f143,f113])).
% 2.01/0.68  fof(f113,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 2.01/0.68    inference(subsumption_resolution,[],[f112,f63])).
% 2.01/0.68  fof(f112,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 2.01/0.68    inference(superposition,[],[f89,f64])).
% 2.01/0.68  fof(f89,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f32])).
% 2.01/0.68  fof(f32,plain,(
% 2.01/0.68    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.01/0.68    inference(flattening,[],[f31])).
% 2.01/0.68  fof(f31,plain,(
% 2.01/0.68    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.01/0.68    inference(ennf_transformation,[],[f7])).
% 2.01/0.68  fof(f7,axiom,(
% 2.01/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 2.01/0.68  fof(f143,plain,(
% 2.01/0.68    ( ! [X0] : (~m1_subset_1(X0,sK2) | k11_lattice3(k2_yellow_1(sK2),X0,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,X0)) )),
% 2.01/0.68    inference(subsumption_resolution,[],[f138,f54])).
% 2.01/0.68  fof(f138,plain,(
% 2.01/0.68    ( ! [X0] : (k11_lattice3(k2_yellow_1(sK2),X0,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,X0) | ~m1_subset_1(X0,sK2) | ~v2_lattice3(k2_yellow_1(sK2))) )),
% 2.01/0.68    inference(resolution,[],[f137,f98])).
% 2.01/0.68  fof(f1604,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~spl6_24),
% 2.01/0.68    inference(resolution,[],[f681,f98])).
% 2.01/0.68  fof(f1080,plain,(
% 2.01/0.68    ~spl6_3 | ~spl6_24 | spl6_27),
% 2.01/0.68    inference(avatar_contradiction_clause,[],[f1079])).
% 2.01/0.68  fof(f1079,plain,(
% 2.01/0.68    $false | (~spl6_3 | ~spl6_24 | spl6_27)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1078,f99])).
% 2.01/0.68  fof(f1078,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,sK2) | (~spl6_3 | ~spl6_24 | spl6_27)),
% 2.01/0.68    inference(forward_demodulation,[],[f1077,f64])).
% 2.01/0.68  fof(f1077,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | ~spl6_24 | spl6_27)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1076,f634])).
% 2.01/0.68  fof(f1076,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.01/0.68    inference(forward_demodulation,[],[f1075,f64])).
% 2.01/0.68  fof(f1075,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1074,f98])).
% 2.01/0.68  fof(f1074,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.01/0.68    inference(forward_demodulation,[],[f1073,f64])).
% 2.01/0.68  fof(f1073,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1072,f223])).
% 2.01/0.68  fof(f223,plain,(
% 2.01/0.68    r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~spl6_3),
% 2.01/0.68    inference(resolution,[],[f154,f72])).
% 2.01/0.68  fof(f72,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_orders_2(X1,X0,X2)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f49])).
% 2.01/0.68  fof(f49,plain,(
% 2.01/0.68    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (~r1_orders_2(X1,sK5(X0,X1,X2,X3),X0) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) & ((! [X5] : (r1_orders_2(X1,X5,X0) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X1,X0,X2) & r1_orders_2(X1,X0,X3)) | ~sP0(X0,X1,X2,X3)))),
% 2.01/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).
% 2.01/0.68  fof(f48,plain,(
% 2.01/0.68    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X1,X4,X0) & r1_orders_2(X1,X4,X2) & r1_orders_2(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) => (~r1_orders_2(X1,sK5(X0,X1,X2,X3),X0) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))))),
% 2.01/0.68    introduced(choice_axiom,[])).
% 2.01/0.68  fof(f47,plain,(
% 2.01/0.68    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (~r1_orders_2(X1,X4,X0) & r1_orders_2(X1,X4,X2) & r1_orders_2(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) & ((! [X5] : (r1_orders_2(X1,X5,X0) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X1,X0,X2) & r1_orders_2(X1,X0,X3)) | ~sP0(X0,X1,X2,X3)))),
% 2.01/0.68    inference(rectify,[],[f46])).
% 2.01/0.68  fof(f46,plain,(
% 2.01/0.68    ! [X3,X0,X2,X1] : ((sP0(X3,X0,X2,X1) | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | ~sP0(X3,X0,X2,X1)))),
% 2.01/0.68    inference(flattening,[],[f45])).
% 2.01/0.68  fof(f45,plain,(
% 2.01/0.68    ! [X3,X0,X2,X1] : ((sP0(X3,X0,X2,X1) | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | ~sP0(X3,X0,X2,X1)))),
% 2.01/0.68    inference(nnf_transformation,[],[f35])).
% 2.01/0.68  fof(f35,plain,(
% 2.01/0.68    ! [X3,X0,X2,X1] : (sP0(X3,X0,X2,X1) <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))),
% 2.01/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.01/0.68  fof(f154,plain,(
% 2.01/0.68    sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4) | ~spl6_3),
% 2.01/0.68    inference(avatar_component_clause,[],[f152])).
% 2.01/0.68  fof(f152,plain,(
% 2.01/0.68    spl6_3 <=> sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4)),
% 2.01/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.01/0.68  fof(f1072,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.01/0.68    inference(subsumption_resolution,[],[f1071,f224])).
% 2.01/0.68  fof(f224,plain,(
% 2.01/0.68    r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~spl6_3),
% 2.01/0.68    inference(resolution,[],[f154,f71])).
% 2.01/0.68  fof(f71,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_orders_2(X1,X0,X3)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f49])).
% 2.01/0.68  fof(f1071,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | spl6_27),
% 2.01/0.68    inference(subsumption_resolution,[],[f1070,f61])).
% 2.01/0.68  fof(f1070,plain,(
% 2.01/0.68    ~v5_orders_2(k2_yellow_1(sK2)) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | spl6_27),
% 2.01/0.68    inference(subsumption_resolution,[],[f1069,f54])).
% 2.01/0.68  fof(f1069,plain,(
% 2.01/0.68    ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | spl6_27),
% 2.01/0.68    inference(subsumption_resolution,[],[f1050,f63])).
% 2.01/0.68  fof(f1050,plain,(
% 2.01/0.68    ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | spl6_27),
% 2.01/0.68    inference(resolution,[],[f378,f741])).
% 2.01/0.68  fof(f741,plain,(
% 2.01/0.68    ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | spl6_27),
% 2.01/0.68    inference(avatar_component_clause,[],[f739])).
% 2.01/0.68  fof(f739,plain,(
% 2.01/0.68    spl6_27 <=> r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.01/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.01/0.68  fof(f378,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (r1_orders_2(X1,X3,k11_lattice3(X1,X0,X2)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_orders_2(X1,X3,X2) | ~r1_orders_2(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 2.01/0.68    inference(resolution,[],[f193,f73])).
% 2.01/0.68  fof(f73,plain,(
% 2.01/0.68    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1)) | r1_orders_2(X1,X5,X0)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f49])).
% 2.01/0.68  fof(f193,plain,(
% 2.01/0.68    ( ! [X6,X4,X5] : (sP0(k11_lattice3(X4,X5,X6),X4,X6,X5) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v2_lattice3(X4) | ~v5_orders_2(X4) | ~m1_subset_1(X6,u1_struct_0(X4))) )),
% 2.01/0.68    inference(subsumption_resolution,[],[f190,f89])).
% 2.01/0.68  fof(f190,plain,(
% 2.01/0.68    ( ! [X6,X4,X5] : (~m1_subset_1(k11_lattice3(X4,X5,X6),u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v2_lattice3(X4) | ~v5_orders_2(X4) | sP0(k11_lattice3(X4,X5,X6),X4,X6,X5)) )),
% 2.01/0.68    inference(resolution,[],[f173,f95])).
% 2.01/0.68  fof(f95,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2,k11_lattice3(X2,X0,X1)) | sP0(k11_lattice3(X2,X0,X1),X2,X1,X0)) )),
% 2.01/0.68    inference(equality_resolution,[],[f69])).
% 2.01/0.68  fof(f69,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0) | k11_lattice3(X2,X0,X1) != X3 | ~sP1(X0,X1,X2,X3)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f44])).
% 2.01/0.68  fof(f44,plain,(
% 2.01/0.68    ! [X0,X1,X2,X3] : (((k11_lattice3(X2,X0,X1) = X3 | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | k11_lattice3(X2,X0,X1) != X3)) | ~sP1(X0,X1,X2,X3))),
% 2.01/0.68    inference(rectify,[],[f43])).
% 2.01/0.68  fof(f43,plain,(
% 2.01/0.68    ! [X1,X2,X0,X3] : (((k11_lattice3(X0,X1,X2) = X3 | ~sP0(X3,X0,X2,X1)) & (sP0(X3,X0,X2,X1) | k11_lattice3(X0,X1,X2) != X3)) | ~sP1(X1,X2,X0,X3))),
% 2.01/0.68    inference(nnf_transformation,[],[f36])).
% 2.01/0.68  fof(f36,plain,(
% 2.01/0.68    ! [X1,X2,X0,X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> sP0(X3,X0,X2,X1)) | ~sP1(X1,X2,X0,X3))),
% 2.01/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.01/0.68  fof(f173,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (sP1(X1,X2,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.01/0.68    inference(subsumption_resolution,[],[f78,f68])).
% 2.01/0.68  fof(f68,plain,(
% 2.01/0.68    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f22])).
% 2.01/0.68  fof(f22,plain,(
% 2.01/0.68    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.01/0.68    inference(flattening,[],[f21])).
% 2.01/0.68  fof(f21,plain,(
% 2.01/0.68    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.01/0.68    inference(ennf_transformation,[],[f6])).
% 2.01/0.68  fof(f6,axiom,(
% 2.01/0.68    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).
% 2.01/0.68  fof(f78,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (sP1(X1,X2,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f37])).
% 2.01/0.68  fof(f37,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP1(X1,X2,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.01/0.68    inference(definition_folding,[],[f24,f36,f35])).
% 2.01/0.68  fof(f24,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.01/0.68    inference(flattening,[],[f23])).
% 2.01/0.68  fof(f23,plain,(
% 2.01/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.01/0.68    inference(ennf_transformation,[],[f8])).
% 2.01/0.68  fof(f8,axiom,(
% 2.01/0.68    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).
% 2.01/0.68  fof(f758,plain,(
% 2.01/0.68    ~spl6_27 | spl6_29 | ~spl6_3 | ~spl6_24),
% 2.01/0.68    inference(avatar_split_clause,[],[f753,f633,f152,f755,f739])).
% 2.01/0.68  fof(f753,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | (~spl6_3 | ~spl6_24)),
% 2.01/0.68    inference(subsumption_resolution,[],[f752,f634])).
% 2.01/0.68  fof(f752,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_3),
% 2.01/0.68    inference(forward_demodulation,[],[f751,f64])).
% 2.01/0.68  fof(f751,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(subsumption_resolution,[],[f750,f98])).
% 2.01/0.68  fof(f750,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,sK2) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(forward_demodulation,[],[f749,f64])).
% 2.01/0.68  fof(f749,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(subsumption_resolution,[],[f748,f61])).
% 2.01/0.68  fof(f748,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(subsumption_resolution,[],[f747,f54])).
% 2.01/0.68  fof(f747,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(subsumption_resolution,[],[f719,f63])).
% 2.01/0.68  fof(f719,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(resolution,[],[f449,f224])).
% 2.01/0.68  fof(f449,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~r1_orders_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | k11_lattice3(X1,X2,X0) = X0 | ~r1_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 2.01/0.68    inference(duplicate_literal_removal,[],[f441])).
% 2.01/0.68  fof(f441,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | k11_lattice3(X1,X2,X0) = X0 | ~r1_orders_2(X1,X0,X0) | ~r1_orders_2(X1,X0,X2)) )),
% 2.01/0.68    inference(resolution,[],[f189,f123])).
% 2.01/0.68  fof(f123,plain,(
% 2.01/0.68    ( ! [X4,X5,X3] : (sP0(X3,X4,X3,X5) | ~r1_orders_2(X4,X3,X3) | ~r1_orders_2(X4,X3,X5)) )),
% 2.01/0.68    inference(duplicate_literal_removal,[],[f122])).
% 2.01/0.68  fof(f122,plain,(
% 2.01/0.68    ( ! [X4,X5,X3] : (sP0(X3,X4,X3,X5) | ~r1_orders_2(X4,X3,X3) | ~r1_orders_2(X4,X3,X5) | sP0(X3,X4,X3,X5) | ~r1_orders_2(X4,X3,X3) | ~r1_orders_2(X4,X3,X5)) )),
% 2.01/0.68    inference(resolution,[],[f77,f76])).
% 2.01/0.68  fof(f76,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (r1_orders_2(X1,sK5(X0,X1,X2,X3),X2) | sP0(X0,X1,X2,X3) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f49])).
% 2.01/0.68  fof(f77,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X1,sK5(X0,X1,X2,X3),X0) | sP0(X0,X1,X2,X3) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f49])).
% 2.01/0.68  fof(f189,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | k11_lattice3(X1,X3,X2) = X0) )),
% 2.01/0.68    inference(resolution,[],[f173,f70])).
% 2.01/0.68  fof(f70,plain,(
% 2.01/0.68    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X3,X2,X1,X0) | k11_lattice3(X2,X0,X1) = X3) )),
% 2.01/0.68    inference(cnf_transformation,[],[f44])).
% 2.01/0.68  fof(f746,plain,(
% 2.01/0.68    ~spl6_27 | spl6_28 | ~spl6_3 | ~spl6_24),
% 2.01/0.68    inference(avatar_split_clause,[],[f737,f633,f152,f743,f739])).
% 2.01/0.68  fof(f737,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | (~spl6_3 | ~spl6_24)),
% 2.01/0.68    inference(subsumption_resolution,[],[f736,f634])).
% 2.01/0.68  fof(f736,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_3),
% 2.01/0.68    inference(forward_demodulation,[],[f735,f64])).
% 2.01/0.68  fof(f735,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(subsumption_resolution,[],[f734,f99])).
% 2.01/0.68  fof(f734,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,sK2) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(forward_demodulation,[],[f733,f64])).
% 2.01/0.68  fof(f733,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(subsumption_resolution,[],[f732,f61])).
% 2.01/0.68  fof(f732,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(subsumption_resolution,[],[f731,f54])).
% 2.01/0.68  fof(f731,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(subsumption_resolution,[],[f718,f63])).
% 2.01/0.68  fof(f718,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.01/0.68    inference(resolution,[],[f449,f223])).
% 2.01/0.68  fof(f666,plain,(
% 2.01/0.68    spl6_24),
% 2.01/0.68    inference(avatar_contradiction_clause,[],[f665])).
% 2.01/0.68  fof(f665,plain,(
% 2.01/0.68    $false | spl6_24),
% 2.01/0.68    inference(subsumption_resolution,[],[f664,f99])).
% 2.01/0.68  fof(f664,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,sK2) | spl6_24),
% 2.01/0.68    inference(subsumption_resolution,[],[f663,f98])).
% 2.01/0.68  fof(f663,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,sK2) | ~m1_subset_1(sK3,sK2) | spl6_24),
% 2.01/0.68    inference(resolution,[],[f635,f113])).
% 2.01/0.68  fof(f635,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | spl6_24),
% 2.01/0.68    inference(avatar_component_clause,[],[f633])).
% 2.01/0.68  fof(f221,plain,(
% 2.01/0.68    spl6_4),
% 2.01/0.68    inference(avatar_contradiction_clause,[],[f220])).
% 2.01/0.68  fof(f220,plain,(
% 2.01/0.68    $false | spl6_4),
% 2.01/0.68    inference(subsumption_resolution,[],[f219,f99])).
% 2.01/0.68  fof(f219,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,sK2) | spl6_4),
% 2.01/0.68    inference(subsumption_resolution,[],[f218,f98])).
% 2.01/0.68  fof(f218,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,sK2) | ~m1_subset_1(sK3,sK2) | spl6_4),
% 2.01/0.68    inference(resolution,[],[f201,f113])).
% 2.01/0.68  fof(f201,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | spl6_4),
% 2.01/0.68    inference(subsumption_resolution,[],[f200,f98])).
% 2.01/0.68  fof(f200,plain,(
% 2.01/0.68    ~m1_subset_1(sK4,sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | spl6_4),
% 2.01/0.68    inference(forward_demodulation,[],[f199,f64])).
% 2.01/0.68  fof(f199,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | spl6_4),
% 2.01/0.68    inference(subsumption_resolution,[],[f198,f99])).
% 2.01/0.68  fof(f198,plain,(
% 2.01/0.68    ~m1_subset_1(sK3,sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | spl6_4),
% 2.01/0.68    inference(forward_demodulation,[],[f197,f64])).
% 2.01/0.68  fof(f197,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | spl6_4),
% 2.01/0.68    inference(forward_demodulation,[],[f196,f64])).
% 2.01/0.68  fof(f196,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | spl6_4),
% 2.01/0.68    inference(subsumption_resolution,[],[f195,f61])).
% 2.01/0.68  fof(f195,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | spl6_4),
% 2.01/0.68    inference(subsumption_resolution,[],[f194,f54])).
% 2.01/0.68  fof(f194,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | spl6_4),
% 2.01/0.68    inference(subsumption_resolution,[],[f191,f63])).
% 2.01/0.68  fof(f191,plain,(
% 2.01/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | spl6_4),
% 2.01/0.68    inference(resolution,[],[f173,f158])).
% 2.01/0.68  fof(f158,plain,(
% 2.01/0.68    ~sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | spl6_4),
% 2.01/0.68    inference(avatar_component_clause,[],[f156])).
% 2.01/0.68  fof(f156,plain,(
% 2.01/0.68    spl6_4 <=> sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.01/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.01/0.68  fof(f159,plain,(
% 2.01/0.68    spl6_3 | ~spl6_4),
% 2.01/0.68    inference(avatar_split_clause,[],[f150,f156,f152])).
% 2.01/0.68  fof(f150,plain,(
% 2.01/0.68    ~sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4)),
% 2.01/0.68    inference(superposition,[],[f95,f146])).
% 2.01/0.68  fof(f146,plain,(
% 2.01/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,sK3)),
% 2.01/0.68    inference(resolution,[],[f143,f99])).
% 2.01/0.68  fof(f111,plain,(
% 2.01/0.68    ~spl6_1 | ~spl6_2),
% 2.01/0.68    inference(avatar_split_clause,[],[f102,f108,f104])).
% 2.01/0.68  fof(f102,plain,(
% 2.01/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)),
% 2.01/0.68    inference(resolution,[],[f94,f93])).
% 2.01/0.68  fof(f93,plain,(
% 2.01/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)))),
% 2.01/0.68    inference(definition_unfolding,[],[f57,f92])).
% 2.01/0.68  fof(f92,plain,(
% 2.01/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.01/0.68    inference(definition_unfolding,[],[f82,f91])).
% 2.01/0.68  fof(f91,plain,(
% 2.01/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.01/0.68    inference(definition_unfolding,[],[f83,f87])).
% 2.01/0.68  fof(f87,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f4])).
% 2.01/0.68  fof(f4,axiom,(
% 2.01/0.68    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.01/0.68  fof(f83,plain,(
% 2.01/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f3])).
% 2.01/0.68  fof(f3,axiom,(
% 2.01/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.01/0.68  fof(f82,plain,(
% 2.01/0.68    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f5])).
% 2.01/0.68  fof(f5,axiom,(
% 2.01/0.68    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.01/0.68  fof(f57,plain,(
% 2.01/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))),
% 2.01/0.68    inference(cnf_transformation,[],[f41])).
% 2.01/0.68  fof(f94,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.01/0.68    inference(definition_unfolding,[],[f90,f92])).
% 2.01/0.68  fof(f90,plain,(
% 2.01/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.01/0.68    inference(cnf_transformation,[],[f34])).
% 2.01/0.68  fof(f34,plain,(
% 2.01/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.01/0.68    inference(flattening,[],[f33])).
% 2.01/0.68  fof(f33,plain,(
% 2.01/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.01/0.68    inference(ennf_transformation,[],[f2])).
% 2.01/0.68  fof(f2,axiom,(
% 2.01/0.68    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.01/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.01/0.68  % SZS output end Proof for theBenchmark
% 2.01/0.68  % (417)------------------------------
% 2.01/0.68  % (417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (417)Termination reason: Refutation
% 2.01/0.68  
% 2.01/0.68  % (417)Memory used [KB]: 11769
% 2.01/0.68  % (417)Time elapsed: 0.250 s
% 2.01/0.68  % (417)------------------------------
% 2.01/0.68  % (417)------------------------------
% 2.01/0.68  % (410)Success in time 0.313 s
%------------------------------------------------------------------------------
