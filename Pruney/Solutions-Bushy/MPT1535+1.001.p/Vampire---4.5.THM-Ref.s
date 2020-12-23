%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1535+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:01 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 325 expanded)
%              Number of leaves         :   28 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  603 (1419 expanded)
%              Number of equality atoms :   84 ( 196 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f276,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f65,f70,f75,f87,f108,f113,f149,f153,f182,f197,f201,f216,f226,f246,f252,f258,f260,f275])).

% (7878)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f275,plain,
    ( ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f273,f130])).

fof(f130,plain,
    ( v1_yellow_0(sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl4_11
  <=> v1_yellow_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f273,plain,
    ( ~ v1_yellow_0(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f33,f68])).

fof(f68,plain,
    ( v2_yellow_0(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_5
  <=> v2_yellow_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f33,plain,
    ( ~ v2_yellow_0(sK1)
    | ~ v1_yellow_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( ~ v2_yellow_0(sK1)
        & v2_yellow_0(sK0) )
      | ( ~ v1_yellow_0(sK1)
        & v1_yellow_0(sK0) ) )
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v2_yellow_0(X1)
                & v2_yellow_0(X0) )
              | ( ~ v1_yellow_0(X1)
                & v1_yellow_0(X0) ) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(sK0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(sK0) ) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ( ( ~ v2_yellow_0(X1)
            & v2_yellow_0(sK0) )
          | ( ~ v1_yellow_0(X1)
            & v1_yellow_0(sK0) ) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ( ( ~ v2_yellow_0(sK1)
          & v2_yellow_0(sK0) )
        | ( ~ v1_yellow_0(sK1)
          & v1_yellow_0(sK0) ) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ( ( v2_yellow_0(X0)
                 => v2_yellow_0(X1) )
                & ( v1_yellow_0(X0)
                 => v1_yellow_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ( ( v2_yellow_0(X0)
               => v2_yellow_0(X1) )
              & ( v1_yellow_0(X0)
               => v1_yellow_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_0)).

fof(f260,plain,
    ( ~ spl4_11
    | spl4_4 ),
    inference(avatar_split_clause,[],[f259,f62,f129])).

fof(f62,plain,
    ( spl4_4
  <=> v2_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f259,plain,
    ( ~ v1_yellow_0(sK1)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f31,f63])).

fof(f63,plain,
    ( ~ v2_yellow_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f31,plain,
    ( v2_yellow_0(sK0)
    | ~ v1_yellow_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f258,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | spl4_25 ),
    inference(subsumption_resolution,[],[f256,f50])).

fof(f50,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f256,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl4_3
    | spl4_25 ),
    inference(subsumption_resolution,[],[f254,f60])).

fof(f60,plain,
    ( v1_yellow_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_3
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f254,plain,
    ( ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | spl4_25 ),
    inference(resolution,[],[f251,f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r1_lattice3(X0,u1_struct_0(X0),sK2(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK2(X0))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r1_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r1_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_yellow_0)).

fof(f251,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl4_25
  <=> m1_subset_1(sK2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f252,plain,
    ( ~ spl4_25
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_18
    | ~ spl4_21
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f247,f244,f199,f179,f105,f53,f249])).

fof(f53,plain,
    ( spl4_2
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f105,plain,
    ( spl4_9
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f179,plain,
    ( spl4_18
  <=> u1_orders_2(sK0) = u1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f199,plain,
    ( spl4_21
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2(sK0),u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | r1_lattice3(X0,u1_struct_0(sK0),sK2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f244,plain,
    ( spl4_24
  <=> ! [X0] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f247,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_18
    | ~ spl4_21
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f238,f245])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f244])).

fof(f238,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | r1_lattice3(sK1,u1_struct_0(sK0),sK2(sK0))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f237])).

fof(f237,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | r1_lattice3(sK1,u1_struct_0(sK0),sK2(sK0))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f236,f181])).

fof(f181,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f179])).

fof(f236,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | r1_lattice3(sK1,u1_struct_0(sK0),sK2(sK0))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f233,f55])).

fof(f55,plain,
    ( l1_orders_2(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f233,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | r1_lattice3(sK1,u1_struct_0(sK0),sK2(sK0))
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(superposition,[],[f200,f107])).

fof(f107,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0),u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | r1_lattice3(X0,u1_struct_0(sK0),sK2(sK0)) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f199])).

fof(f246,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_9
    | spl4_11 ),
    inference(avatar_split_clause,[],[f242,f129,f105,f53,f244])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_2
    | ~ spl4_9
    | spl4_11 ),
    inference(subsumption_resolution,[],[f124,f131])).

fof(f131,plain,
    ( ~ v1_yellow_0(sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X0)
        | v1_yellow_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f117,f55])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X0)
        | v1_yellow_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK1) )
    | ~ spl4_9 ),
    inference(superposition,[],[f37,f107])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | v1_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f226,plain,
    ( ~ spl4_4
    | ~ spl4_1
    | spl4_22 ),
    inference(avatar_split_clause,[],[f223,f213,f48,f62])).

fof(f213,plain,
    ( spl4_22
  <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f223,plain,
    ( ~ v2_yellow_0(sK0)
    | ~ spl4_1
    | spl4_22 ),
    inference(subsumption_resolution,[],[f218,f50])).

fof(f218,plain,
    ( ~ v2_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | spl4_22 ),
    inference(resolution,[],[f215,f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r2_lattice3(X0,u1_struct_0(X0),sK3(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r2_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,u1_struct_0(X0),sK3(X0))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r2_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r2_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_0)).

fof(f215,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f213])).

fof(f216,plain,
    ( ~ spl4_22
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f211,f195,f179,f151,f105,f53,f213])).

fof(f151,plain,
    ( spl4_15
  <=> ! [X1] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f195,plain,
    ( spl4_20
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3(sK0),u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | r2_lattice3(X0,u1_struct_0(sK0),sK3(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f211,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f210])).

fof(f210,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f209,f181])).

fof(f209,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f208,f152])).

fof(f152,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f208,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | r2_lattice3(sK1,u1_struct_0(sK0),sK3(sK0))
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f205,f55])).

fof(f205,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | r2_lattice3(sK1,u1_struct_0(sK0),sK3(sK0))
    | ~ spl4_9
    | ~ spl4_20 ),
    inference(superposition,[],[f196,f107])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0),u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | r2_lattice3(X0,u1_struct_0(sK0),sK3(sK0)) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f195])).

fof(f201,plain,
    ( spl4_21
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f158,f58,f48,f199])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0),u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | r1_lattice3(X0,u1_struct_0(sK0),sK2(sK0)) )
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f157,f50])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0),u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK0)
        | r1_lattice3(X0,u1_struct_0(sK0),sK2(sK0)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f60,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(X1)
      | ~ m1_subset_1(sK2(X1),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | r1_lattice3(X0,u1_struct_0(X1),sK2(X1)) ) ),
    inference(subsumption_resolution,[],[f89,f35])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,u1_struct_0(X1),sK2(X1))
      | ~ m1_subset_1(sK2(X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK2(X1),u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ v1_yellow_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,u1_struct_0(X1),sK2(X1))
      | ~ m1_subset_1(sK2(X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK2(X1),u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ v1_yellow_0(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r1_lattice3(X0,u1_struct_0(X0),sK2(X0))
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,X4)
      | r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f197,plain,
    ( spl4_20
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f138,f62,f48,f195])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0),u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | r2_lattice3(X0,u1_struct_0(sK0),sK3(sK0)) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f137,f50])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0),u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK0)
        | r2_lattice3(X0,u1_struct_0(sK0),sK3(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f97,f64])).

fof(f64,plain,
    ( v2_yellow_0(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v2_yellow_0(X1)
      | ~ m1_subset_1(sK3(X1),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | r2_lattice3(X0,u1_struct_0(X1),sK3(X1)) ) ),
    inference(subsumption_resolution,[],[f96,f38])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,u1_struct_0(X1),sK3(X1))
      | ~ m1_subset_1(sK3(X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X1),u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ v2_yellow_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,u1_struct_0(X1),sK3(X1))
      | ~ m1_subset_1(sK3(X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X1),u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ v2_yellow_0(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_lattice3(X0,u1_struct_0(X0),sK3(X0))
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,X4)
      | r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f182,plain,
    ( spl4_18
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f177,f147,f110,f179])).

fof(f110,plain,
    ( spl4_10
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f147,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( u1_orders_2(sK0) = X0
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f177,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(superposition,[],[f148,f112])).

fof(f112,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0)
        | u1_orders_2(sK0) = X0 )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f153,plain,
    ( spl4_15
    | ~ spl4_2
    | spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f126,f105,f67,f53,f151])).

fof(f126,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_2
    | spl4_5
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f125,f55])).

fof(f125,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK1) )
    | spl4_5
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f120,f69])).

fof(f69,plain,
    ( ~ v2_yellow_0(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f120,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X1)
        | v2_yellow_0(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK1) )
    | ~ spl4_9 ),
    inference(superposition,[],[f40,f107])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
      | v2_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f149,plain,
    ( spl4_14
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f101,f48,f147])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( u1_orders_2(sK0) = X0
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f83,f50])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_orders_2(X0) = X2
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f113,plain,
    ( spl4_10
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f103,f85,f72,f110])).

fof(f72,plain,
    ( spl4_6
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f85,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( u1_struct_0(sK0) = X0
        | g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f103,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f74,f100])).

fof(f100,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(superposition,[],[f86,f74])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X0 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f74,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f108,plain,
    ( spl4_9
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f100,f85,f72,f105])).

fof(f87,plain,
    ( spl4_7
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f81,f48,f85])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(sK0) = X0
        | g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f80,f50])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) ),
    inference(resolution,[],[f43,f34])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f32,f67,f58])).

fof(f32,plain,
    ( ~ v2_yellow_0(sK1)
    | v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f30,f62,f58])).

fof(f30,plain,
    ( v2_yellow_0(sK0)
    | v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
