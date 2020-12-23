%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1574+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 457 expanded)
%              Number of leaves         :   23 ( 174 expanded)
%              Depth                    :   14
%              Number of atoms          :  456 (2159 expanded)
%              Number of equality atoms :   20 ( 306 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f56,f62,f72,f78,f97,f103,f107,f113,f123,f129,f148,f157,f164,f180,f190,f200])).

fof(f200,plain,
    ( ~ spl4_21
    | ~ spl4_1
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f199,f145,f40,f187])).

fof(f187,plain,
    ( spl4_21
  <=> r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f40,plain,
    ( spl4_1
  <=> r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f145,plain,
    ( spl4_17
  <=> r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f199,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl4_1
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f198,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    & ( r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | r2_yellow_0(sK0,sK1) )
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r2_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow_0(sK0,X1) != k2_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
          & ( r2_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
            | r2_yellow_0(sK0,X1) ) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( k2_yellow_0(sK0,X1) != k2_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
        & ( r2_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
          | r2_yellow_0(sK0,X1) ) )
   => ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      & ( r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r2_yellow_0(X0,X1) )
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_yellow_0)).

fof(f198,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f197,f20])).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f197,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f196,f42])).

fof(f42,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f196,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f185,f32])).

fof(f32,plain,(
    ~ sQ3_eqProxy(k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    inference(equality_proxy_replacement,[],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f22,plain,(
    k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f185,plain,
    ( sQ3_eqProxy(k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f147,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | sQ3_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f29,f31])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_yellow_0)).

fof(f147,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f190,plain,
    ( spl4_21
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f183,f145,f121,f187])).

fof(f121,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f183,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(resolution,[],[f147,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f180,plain,
    ( ~ spl4_2
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f179,f161,f154,f44])).

fof(f44,plain,
    ( spl4_2
  <=> r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f154,plain,
    ( spl4_18
  <=> r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f161,plain,
    ( spl4_19
  <=> r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f179,plain,
    ( ~ r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f178,f19])).

fof(f178,plain,
    ( ~ r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f173,f20])).

fof(f173,plain,
    ( ~ r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f172,f156])).

fof(f156,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f172,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f171,f48])).

fof(f48,plain,(
    ~ sQ3_eqProxy(k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))),k2_yellow_0(sK0,sK1)) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f171,plain,
    ( sQ3_eqProxy(k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))),k2_yellow_0(sK0,sK1))
    | ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_19 ),
    inference(resolution,[],[f163,f33])).

fof(f163,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f164,plain,
    ( spl4_19
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f158,f154,f70,f161])).

fof(f70,plain,
    ( spl4_5
  <=> ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f158,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(resolution,[],[f156,f71])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f157,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f152,f95,f76,f154])).

fof(f76,plain,
    ( spl4_6
  <=> ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f95,plain,
    ( spl4_9
  <=> ! [X0] :
        ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | sQ3_eqProxy(k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))),k2_yellow_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f152,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f151,f77])).

fof(f77,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f151,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl4_9 ),
    inference(resolution,[],[f96,f48])).

fof(f96,plain,
    ( ! [X0] :
        ( sQ3_eqProxy(k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))),k2_yellow_0(sK0,X0))
        | r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0)) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f95])).

% (11272)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (11276)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (11283)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (11273)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f148,plain,
    ( spl4_17
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f143,f127,f101,f145])).

fof(f101,plain,
    ( spl4_10
  <=> ! [X0] :
        ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | sQ3_eqProxy(k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f127,plain,
    ( spl4_14
  <=> ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f143,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f142,f128])).

fof(f128,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f142,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl4_10 ),
    inference(resolution,[],[f102,f32])).

fof(f102,plain,
    ( ! [X0] :
        ( sQ3_eqProxy(k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,X0))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | r1_lattice3(sK0,sK1,sK2(sK0,sK1,X0)) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f129,plain,
    ( spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f125,f110,f127])).

fof(f110,plain,
    ( spl4_12
  <=> m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

% (11274)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f125,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) )
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f124,f19])).

fof(f124,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f115,f20])).

fof(f115,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_12 ),
    inference(resolution,[],[f112,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow_0)).

fof(f112,plain,
    ( m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f123,plain,
    ( spl4_13
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f119,f110,f121])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) )
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f118,f19])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f114,f20])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_12 ),
    inference(resolution,[],[f112,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f113,plain,
    ( spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f108,f105,f110])).

fof(f105,plain,
    ( spl4_11
  <=> ! [X1] :
        ( m1_subset_1(sK2(sK0,sK1,X1),u1_struct_0(sK0))
        | sQ3_eqProxy(k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f108,plain,
    ( m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_11 ),
    inference(resolution,[],[f106,f32])).

fof(f106,plain,
    ( ! [X1] :
        ( sQ3_eqProxy(k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,X1))
        | m1_subset_1(sK2(sK0,sK1,X1),u1_struct_0(sK0)) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl4_11
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f99,f40,f105])).

fof(f99,plain,
    ( ! [X1] :
        ( m1_subset_1(sK2(sK0,sK1,X1),u1_struct_0(sK0))
        | sQ3_eqProxy(k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,X1)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK0,X0)
      | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
      | sQ3_eqProxy(k2_yellow_0(sK0,X0),k2_yellow_0(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f50,f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,X0)
      | sQ3_eqProxy(k2_yellow_0(sK0,X0),k2_yellow_0(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f35,f20])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | sQ3_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f27,f31])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,
    ( spl4_10
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f98,f40,f101])).

fof(f98,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | sQ3_eqProxy(k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,X0)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f42,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK0,X1)
      | r1_lattice3(sK0,X1,sK2(sK0,X1,X0))
      | r1_lattice3(sK0,X0,sK2(sK0,X1,X0))
      | sQ3_eqProxy(k2_yellow_0(sK0,X1),k2_yellow_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f91,f19])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_lattice3(sK0,X0,sK2(sK0,X1,X0))
      | r1_lattice3(sK0,X1,sK2(sK0,X1,X0))
      | ~ r2_yellow_0(sK0,X1)
      | sQ3_eqProxy(k2_yellow_0(sK0,X1),k2_yellow_0(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f34,f20])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | sQ3_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f31])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f97,plain,
    ( spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f93,f44,f95])).

fof(f93,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | sQ3_eqProxy(k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))),k2_yellow_0(sK0,X0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f92,f46])).

fof(f46,plain,
    ( r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f78,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f74,f59,f76])).

fof(f59,plain,
    ( spl4_4
  <=> m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f73,f19])).

fof(f73,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f64,f20])).

fof(f64,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f61,f25])).

fof(f61,plain,
    ( m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f72,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f68,f59,f70])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f67,f19])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f63,f20])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f61,f26])).

fof(f62,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f57,f54,f59])).

fof(f54,plain,
    ( spl4_3
  <=> ! [X0] :
        ( m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0),u1_struct_0(sK0))
        | sQ3_eqProxy(k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))),k2_yellow_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f57,plain,
    ( m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f55,f48])).

fof(f55,plain,
    ( ! [X0] :
        ( sQ3_eqProxy(k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))),k2_yellow_0(sK0,X0))
        | m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0),u1_struct_0(sK0)) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f52,f44,f54])).

fof(f52,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0),u1_struct_0(sK0))
        | sQ3_eqProxy(k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))),k2_yellow_0(sK0,X0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f51,f46])).

fof(f47,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f21,f44,f40])).

fof(f21,plain,
    ( r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
