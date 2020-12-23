%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 363 expanded)
%              Number of leaves         :   53 ( 147 expanded)
%              Depth                    :   11
%              Number of atoms          :  897 (2194 expanded)
%              Number of equality atoms :   40 (  56 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f611,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f123,f128,f133,f138,f143,f153,f158,f168,f170,f176,f189,f225,f243,f244,f259,f332,f339,f343,f364,f372,f393,f397,f444,f488,f489,f490,f565,f598,f609,f610])).

fof(f610,plain,
    ( u1_struct_0(sK0) != sK1
    | m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f609,plain,
    ( ~ spl8_16
    | ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | ~ spl8_16
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f198,f192,f103])).

fof(f103,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f192,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl8_16
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f198,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl8_17
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f598,plain,
    ( spl8_15
    | ~ spl8_11
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f572,f562,f155,f186])).

fof(f186,plain,
    ( spl8_15
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f155,plain,
    ( spl8_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f562,plain,
    ( spl8_50
  <=> r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f572,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl8_11
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f570,f157])).

fof(f157,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f570,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_50 ),
    inference(resolution,[],[f564,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f564,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f562])).

fof(f565,plain,
    ( spl8_50
    | ~ spl8_22
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f525,f486,f240,f562])).

fof(f240,plain,
    ( spl8_22
  <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f486,plain,
    ( spl8_44
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f525,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1)
    | ~ spl8_22
    | ~ spl8_44 ),
    inference(resolution,[],[f487,f242])).

fof(f242,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f240])).

fof(f487,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f486])).

fof(f490,plain,
    ( u1_struct_0(sK0) != sK1
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f489,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f488,plain,
    ( spl8_44
    | ~ spl8_13
    | ~ spl8_39
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f474,f442,f395,f165,f486])).

fof(f165,plain,
    ( spl8_13
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f395,plain,
    ( spl8_39
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f442,plain,
    ( spl8_42
  <=> ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl8_13
    | ~ spl8_39
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f473,f166])).

fof(f166,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f473,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl8_39
    | ~ spl8_42 ),
    inference(duplicate_literal_removal,[],[f470])).

fof(f470,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl8_39
    | ~ spl8_42 ),
    inference(resolution,[],[f443,f396])).

fof(f396,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1) )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f395])).

fof(f443,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f442])).

% (26464)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f444,plain,
    ( spl8_42
    | ~ spl8_14
    | ~ spl8_31
    | ~ spl8_35
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f411,f391,f341,f321,f173,f442])).

fof(f173,plain,
    ( spl8_14
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f321,plain,
    ( spl8_31
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f341,plain,
    ( spl8_35
  <=> ! [X1,X0] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f391,plain,
    ( spl8_38
  <=> ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f411,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_14
    | ~ spl8_31
    | ~ spl8_35
    | ~ spl8_38 ),
    inference(forward_demodulation,[],[f410,f175])).

fof(f175,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f173])).

fof(f410,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) )
    | ~ spl8_31
    | ~ spl8_35
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f409,f323])).

fof(f323,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f321])).

fof(f409,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) )
    | ~ spl8_35
    | ~ spl8_38 ),
    inference(duplicate_literal_removal,[],[f398])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) )
    | ~ spl8_35
    | ~ spl8_38 ),
    inference(resolution,[],[f392,f342])).

fof(f342,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f341])).

fof(f392,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f391])).

fof(f397,plain,
    ( spl8_39
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f389,f370,f155,f150,f395])).

fof(f150,plain,
    ( spl8_10
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f370,plain,
    ( spl8_37
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1) )
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f388,f157])).

fof(f388,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK1) )
    | ~ spl8_10
    | ~ spl8_37 ),
    inference(resolution,[],[f371,f152])).

fof(f152,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f371,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X2,sK0)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f370])).

fof(f393,plain,
    ( spl8_38
    | ~ spl8_8
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f344,f337,f140,f391])).

fof(f140,plain,
    ( spl8_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f337,plain,
    ( spl8_34
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,X0)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f344,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_8
    | ~ spl8_34 ),
    inference(resolution,[],[f338,f142])).

fof(f142,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f337])).

fof(f372,plain,
    ( spl8_37
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f313,f130,f370])).

fof(f130,plain,
    ( spl8_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f313,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f308,f132])).

fof(f132,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f308,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(subsumption_resolution,[],[f72,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f72,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK2(X0,X1),X3)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f364,plain,
    ( spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_31 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_31 ),
    inference(subsumption_resolution,[],[f362,f107])).

fof(f107,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f362,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_31 ),
    inference(subsumption_resolution,[],[f361,f122])).

fof(f122,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f361,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | spl8_31 ),
    inference(subsumption_resolution,[],[f360,f127])).

fof(f127,plain,
    ( v1_yellow_0(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_5
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f360,plain,
    ( ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | spl8_31 ),
    inference(subsumption_resolution,[],[f358,f132])).

fof(f358,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_31 ),
    inference(resolution,[],[f322,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f322,plain,
    ( ~ r1_yellow_0(sK0,k1_xboole_0)
    | spl8_31 ),
    inference(avatar_component_clause,[],[f321])).

fof(f343,plain,
    ( spl8_35
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f306,f130,f120,f341])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f305,f132])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X0)
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl8_4 ),
    inference(resolution,[],[f291,f122])).

fof(f291,plain,(
    ! [X4,X2,X0] :
      ( ~ v5_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k1_yellow_0(X0,X2),X4) ) ),
    inference(subsumption_resolution,[],[f101,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f101,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X1,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
        & r2_lattice3(X0,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f339,plain,
    ( spl8_34
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f335,f330,f337])).

fof(f330,plain,
    ( spl8_33
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,X0)
        | ~ v1_xboole_0(X1) )
    | ~ spl8_33 ),
    inference(resolution,[],[f331,f92])).

fof(f92,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f331,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f330])).

fof(f332,plain,
    ( spl8_33
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f249,f130,f330])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f80,f132])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

% (26459)Refutation not found, incomplete strategy% (26459)------------------------------
% (26459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26459)Termination reason: Refutation not found, incomplete strategy

% (26459)Memory used [KB]: 1663
fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (26459)Time elapsed: 0.084 s
% (26459)------------------------------
% (26459)------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f259,plain,
    ( spl8_23
    | spl8_24
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f229,f222,f256,f252])).

fof(f252,plain,
    ( spl8_23
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f256,plain,
    ( spl8_24
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f222,plain,
    ( spl8_19
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f229,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_19 ),
    inference(resolution,[],[f224,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f224,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f244,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_subset_1(sK1,sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f243,plain,
    ( spl8_22
    | ~ spl8_11
    | spl8_15 ),
    inference(avatar_split_clause,[],[f228,f186,f155,f240])).

fof(f228,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl8_11
    | spl8_15 ),
    inference(subsumption_resolution,[],[f227,f187])).

fof(f187,plain,
    ( u1_struct_0(sK0) != sK1
    | spl8_15 ),
    inference(avatar_component_clause,[],[f186])).

fof(f227,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1
    | ~ spl8_11 ),
    inference(resolution,[],[f96,f157])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f225,plain,
    ( spl8_19
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f180,f173,f130,f222])).

fof(f180,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f179,f132])).

fof(f179,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl8_14 ),
    inference(superposition,[],[f94,f175])).

fof(f189,plain,
    ( spl8_15
    | ~ spl8_11
    | spl8_12 ),
    inference(avatar_split_clause,[],[f182,f161,f155,f186])).

fof(f161,plain,
    ( spl8_12
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f182,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl8_11
    | spl8_12 ),
    inference(subsumption_resolution,[],[f181,f162])).

fof(f162,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f181,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_11 ),
    inference(resolution,[],[f99,f157])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f176,plain,
    ( spl8_14
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f171,f130,f173])).

fof(f171,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_6 ),
    inference(resolution,[],[f71,f132])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f170,plain,
    ( ~ spl8_12
    | spl8_13 ),
    inference(avatar_split_clause,[],[f169,f165,f161])).

fof(f169,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl8_13 ),
    inference(subsumption_resolution,[],[f69,f167])).

fof(f167,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f69,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & v2_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & v2_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & v2_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & v2_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f168,plain,
    ( spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f68,f165,f161])).

fof(f68,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f158,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f67,f155])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f153,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f66,f150])).

fof(f66,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f143,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f70,f140])).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f138,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f64,f135])).

fof(f135,plain,
    ( spl8_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f133,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f63,f130])).

fof(f63,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f128,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f62,f125])).

fof(f62,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f123,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f61,f120])).

fof(f61,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f58,f105])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (26455)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (26453)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (26456)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (26454)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (26462)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (26461)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (26452)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (26457)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (26476)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (26471)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (26472)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (26463)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (26470)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (26466)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (26475)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (26452)Refutation not found, incomplete strategy% (26452)------------------------------
% 0.20/0.53  % (26452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26452)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26452)Memory used [KB]: 10618
% 0.20/0.53  % (26452)Time elapsed: 0.115 s
% 0.20/0.53  % (26452)------------------------------
% 0.20/0.53  % (26452)------------------------------
% 0.20/0.53  % (26473)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (26469)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (26459)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (26454)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f611,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f108,f123,f128,f133,f138,f143,f153,f158,f168,f170,f176,f189,f225,f243,f244,f259,f332,f339,f343,f364,f372,f393,f397,f444,f488,f489,f490,f565,f598,f609,f610])).
% 0.20/0.53  fof(f610,plain,(
% 0.20/0.53    u1_struct_0(sK0) != sK1 | m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f609,plain,(
% 0.20/0.53    ~spl8_16 | ~spl8_17),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f608])).
% 0.20/0.53  fof(f608,plain,(
% 0.20/0.53    $false | (~spl8_16 | ~spl8_17)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f198,f192,f103])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    v1_subset_1(sK1,sK1) | ~spl8_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f191])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    spl8_16 <=> v1_subset_1(sK1,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl8_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f196])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    spl8_17 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.53  fof(f598,plain,(
% 0.20/0.53    spl8_15 | ~spl8_11 | ~spl8_50),
% 0.20/0.53    inference(avatar_split_clause,[],[f572,f562,f155,f186])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    spl8_15 <=> u1_struct_0(sK0) = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    spl8_11 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.53  fof(f562,plain,(
% 0.20/0.53    spl8_50 <=> r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.20/0.53  fof(f572,plain,(
% 0.20/0.53    u1_struct_0(sK0) = sK1 | (~spl8_11 | ~spl8_50)),
% 0.20/0.53    inference(subsumption_resolution,[],[f570,f157])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f155])).
% 0.20/0.53  fof(f570,plain,(
% 0.20/0.53    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_50),
% 0.20/0.53    inference(resolution,[],[f564,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(flattening,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.20/0.53  fof(f564,plain,(
% 0.20/0.53    r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1) | ~spl8_50),
% 0.20/0.53    inference(avatar_component_clause,[],[f562])).
% 0.20/0.53  fof(f565,plain,(
% 0.20/0.53    spl8_50 | ~spl8_22 | ~spl8_44),
% 0.20/0.53    inference(avatar_split_clause,[],[f525,f486,f240,f562])).
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    spl8_22 <=> m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.20/0.53  fof(f486,plain,(
% 0.20/0.53    spl8_44 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 0.20/0.53  fof(f525,plain,(
% 0.20/0.53    r2_hidden(sK7(u1_struct_0(sK0),sK1),sK1) | (~spl8_22 | ~spl8_44)),
% 0.20/0.53    inference(resolution,[],[f487,f242])).
% 0.20/0.53  fof(f242,plain,(
% 0.20/0.53    m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl8_22),
% 0.20/0.53    inference(avatar_component_clause,[],[f240])).
% 0.20/0.53  fof(f487,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | ~spl8_44),
% 0.20/0.53    inference(avatar_component_clause,[],[f486])).
% 0.20/0.53  fof(f490,plain,(
% 0.20/0.53    u1_struct_0(sK0) != sK1 | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f489,plain,(
% 0.20/0.53    u1_struct_0(sK0) != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f488,plain,(
% 0.20/0.53    spl8_44 | ~spl8_13 | ~spl8_39 | ~spl8_42),
% 0.20/0.53    inference(avatar_split_clause,[],[f474,f442,f395,f165,f486])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    spl8_13 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.53  fof(f395,plain,(
% 0.20/0.53    spl8_39 <=> ! [X1,X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.20/0.53  fof(f442,plain,(
% 0.20/0.53    spl8_42 <=> ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 0.20/0.53  fof(f474,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | (~spl8_13 | ~spl8_39 | ~spl8_42)),
% 0.20/0.53    inference(subsumption_resolution,[],[f473,f166])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl8_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f165])).
% 0.20/0.53  fof(f473,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1)) ) | (~spl8_39 | ~spl8_42)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f470])).
% 0.20/0.53  fof(f470,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1)) ) | (~spl8_39 | ~spl8_42)),
% 0.20/0.53    inference(resolution,[],[f443,f396])).
% 0.20/0.53  fof(f396,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | r2_hidden(X1,sK1)) ) | ~spl8_39),
% 0.20/0.53    inference(avatar_component_clause,[],[f395])).
% 0.20/0.53  fof(f443,plain,(
% 0.20/0.53    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_42),
% 0.20/0.53    inference(avatar_component_clause,[],[f442])).
% 0.20/0.53  % (26464)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  fof(f444,plain,(
% 0.20/0.53    spl8_42 | ~spl8_14 | ~spl8_31 | ~spl8_35 | ~spl8_38),
% 0.20/0.53    inference(avatar_split_clause,[],[f411,f391,f341,f321,f173,f442])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    spl8_14 <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.53  fof(f321,plain,(
% 0.20/0.53    spl8_31 <=> r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.20/0.53  fof(f341,plain,(
% 0.20/0.53    spl8_35 <=> ! [X1,X0] : (~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.20/0.53  fof(f391,plain,(
% 0.20/0.53    spl8_38 <=> ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.20/0.53  fof(f411,plain,(
% 0.20/0.53    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_14 | ~spl8_31 | ~spl8_35 | ~spl8_38)),
% 0.20/0.53    inference(forward_demodulation,[],[f410,f175])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f173])).
% 0.20/0.53  fof(f410,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)) ) | (~spl8_31 | ~spl8_35 | ~spl8_38)),
% 0.20/0.53    inference(subsumption_resolution,[],[f409,f323])).
% 0.20/0.53  fof(f323,plain,(
% 0.20/0.53    r1_yellow_0(sK0,k1_xboole_0) | ~spl8_31),
% 0.20/0.53    inference(avatar_component_clause,[],[f321])).
% 0.20/0.53  fof(f409,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)) ) | (~spl8_35 | ~spl8_38)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f398])).
% 0.20/0.53  fof(f398,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)) ) | (~spl8_35 | ~spl8_38)),
% 0.20/0.53    inference(resolution,[],[f392,f342])).
% 0.20/0.53  fof(f342,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) ) | ~spl8_35),
% 0.20/0.53    inference(avatar_component_clause,[],[f341])).
% 0.20/0.53  fof(f392,plain,(
% 0.20/0.53    ( ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_38),
% 0.20/0.53    inference(avatar_component_clause,[],[f391])).
% 0.20/0.53  fof(f397,plain,(
% 0.20/0.53    spl8_39 | ~spl8_10 | ~spl8_11 | ~spl8_37),
% 0.20/0.53    inference(avatar_split_clause,[],[f389,f370,f155,f150,f395])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    spl8_10 <=> v13_waybel_0(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.53  fof(f370,plain,(
% 0.20/0.53    spl8_37 <=> ! [X1,X0,X2] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.20/0.53  fof(f389,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1)) ) | (~spl8_10 | ~spl8_11 | ~spl8_37)),
% 0.20/0.53    inference(subsumption_resolution,[],[f388,f157])).
% 0.20/0.53  fof(f388,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1)) ) | (~spl8_10 | ~spl8_37)),
% 0.20/0.53    inference(resolution,[],[f371,f152])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    v13_waybel_0(sK1,sK0) | ~spl8_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f150])).
% 0.20/0.53  fof(f371,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v13_waybel_0(X2,sK0) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl8_37),
% 0.20/0.53    inference(avatar_component_clause,[],[f370])).
% 0.20/0.53  fof(f393,plain,(
% 0.20/0.53    spl8_38 | ~spl8_8 | ~spl8_34),
% 0.20/0.53    inference(avatar_split_clause,[],[f344,f337,f140,f391])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    spl8_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.53  fof(f337,plain,(
% 0.20/0.53    spl8_34 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,X1,X0) | ~v1_xboole_0(X1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.20/0.53  fof(f344,plain,(
% 0.20/0.53    ( ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_8 | ~spl8_34)),
% 0.20/0.53    inference(resolution,[],[f338,f142])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0) | ~spl8_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f140])).
% 0.20/0.53  fof(f338,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_xboole_0(X1) | r2_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f337])).
% 0.20/0.53  fof(f372,plain,(
% 0.20/0.53    spl8_37 | ~spl8_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f313,f130,f370])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    spl8_6 <=> l1_orders_2(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.53  fof(f313,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl8_6),
% 0.20/0.53    inference(resolution,[],[f308,f132])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    l1_orders_2(sK0) | ~spl8_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f130])).
% 0.20/0.53  fof(f308,plain,(
% 0.20/0.53    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f72,f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(rectify,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.53  fof(f364,plain,(
% 0.20/0.53    spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_31),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f363])).
% 0.20/0.53  fof(f363,plain,(
% 0.20/0.53    $false | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f362,f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    ~v2_struct_0(sK0) | spl8_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    spl8_1 <=> v2_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.53  fof(f362,plain,(
% 0.20/0.53    v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f361,f122])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    v5_orders_2(sK0) | ~spl8_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f120])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    spl8_4 <=> v5_orders_2(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.53  fof(f361,plain,(
% 0.20/0.53    ~v5_orders_2(sK0) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_6 | spl8_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f360,f127])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    v1_yellow_0(sK0) | ~spl8_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f125])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    spl8_5 <=> v1_yellow_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.53  fof(f360,plain,(
% 0.20/0.53    ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | (~spl8_6 | spl8_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f358,f132])).
% 0.20/0.53  fof(f358,plain,(
% 0.20/0.53    ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl8_31),
% 0.20/0.53    inference(resolution,[],[f322,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.20/0.53  fof(f322,plain,(
% 0.20/0.53    ~r1_yellow_0(sK0,k1_xboole_0) | spl8_31),
% 0.20/0.53    inference(avatar_component_clause,[],[f321])).
% 0.20/0.53  fof(f343,plain,(
% 0.20/0.53    spl8_35 | ~spl8_4 | ~spl8_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f306,f130,f120,f341])).
% 0.20/0.53  fof(f306,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) ) | (~spl8_4 | ~spl8_6)),
% 0.20/0.53    inference(subsumption_resolution,[],[f305,f132])).
% 0.20/0.53  fof(f305,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,X0) | ~l1_orders_2(sK0) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) ) | ~spl8_4),
% 0.20/0.53    inference(resolution,[],[f291,f122])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    ( ! [X4,X2,X0] : (~v5_orders_2(X0) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | ~l1_orders_2(X0) | r1_orders_2(X0,k1_yellow_0(X0,X2),X4)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f101,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X4,X2,X0] : (r1_orders_2(X0,k1_yellow_0(X0,X2),X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK5(X0,X1,X2)) & r2_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK5(X0,X1,X2)) & r2_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.53    inference(rectify,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.20/0.53  fof(f339,plain,(
% 0.20/0.53    spl8_34 | ~spl8_33),
% 0.20/0.53    inference(avatar_split_clause,[],[f335,f330,f337])).
% 0.20/0.53  fof(f330,plain,(
% 0.20/0.53    spl8_33 <=> ! [X1,X0] : (r2_hidden(sK4(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.20/0.53  fof(f335,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,X1,X0) | ~v1_xboole_0(X1)) ) | ~spl8_33),
% 0.20/0.53    inference(resolution,[],[f331,f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(rectify,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.53  fof(f331,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl8_33),
% 0.20/0.53    inference(avatar_component_clause,[],[f330])).
% 0.20/0.53  fof(f332,plain,(
% 0.20/0.53    spl8_33 | ~spl8_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f249,f130,f330])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl8_6),
% 0.20/0.53    inference(resolution,[],[f80,f132])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(rectify,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  % (26459)Refutation not found, incomplete strategy% (26459)------------------------------
% 0.20/0.53  % (26459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26459)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26459)Memory used [KB]: 1663
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  % (26459)Time elapsed: 0.084 s
% 0.20/0.53  % (26459)------------------------------
% 0.20/0.53  % (26459)------------------------------
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    spl8_23 | spl8_24 | ~spl8_19),
% 0.20/0.53    inference(avatar_split_clause,[],[f229,f222,f256,f252])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    spl8_23 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    spl8_24 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    spl8_19 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl8_19),
% 0.20/0.53    inference(resolution,[],[f224,f95])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.53  fof(f224,plain,(
% 0.20/0.53    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl8_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f222])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    u1_struct_0(sK0) != sK1 | v1_subset_1(sK1,sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f243,plain,(
% 0.20/0.53    spl8_22 | ~spl8_11 | spl8_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f228,f186,f155,f240])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl8_11 | spl8_15)),
% 0.20/0.53    inference(subsumption_resolution,[],[f227,f187])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    u1_struct_0(sK0) != sK1 | spl8_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f186])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    m1_subset_1(sK7(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1 | ~spl8_11),
% 0.20/0.53    inference(resolution,[],[f96,f157])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK7(X0,X1),X0) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f56])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    spl8_19 | ~spl8_6 | ~spl8_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f180,f173,f130,f222])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | (~spl8_6 | ~spl8_14)),
% 0.20/0.53    inference(subsumption_resolution,[],[f179,f132])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl8_14),
% 0.20/0.53    inference(superposition,[],[f94,f175])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    spl8_15 | ~spl8_11 | spl8_12),
% 0.20/0.53    inference(avatar_split_clause,[],[f182,f161,f155,f186])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    spl8_12 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    u1_struct_0(sK0) = sK1 | (~spl8_11 | spl8_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f181,f162])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl8_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f161])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_11),
% 0.20/0.53    inference(resolution,[],[f99,f157])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f57])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    spl8_14 | ~spl8_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f171,f130,f173])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_6),
% 0.20/0.53    inference(resolution,[],[f71,f132])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    ~spl8_12 | spl8_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f169,f165,f161])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl8_13),
% 0.20/0.53    inference(subsumption_resolution,[],[f69,f167])).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl8_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f165])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f13])).
% 0.20/0.53  fof(f13,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    spl8_12 | ~spl8_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f68,f165,f161])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    spl8_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f67,f155])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    spl8_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f66,f150])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    v13_waybel_0(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    spl8_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f70,f140])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    ~spl8_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f64,f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    spl8_7 <=> v1_xboole_0(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ~v1_xboole_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    spl8_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f63,f130])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    l1_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    spl8_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f62,f125])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    v1_yellow_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    spl8_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f61,f120])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    v5_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ~spl8_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f58,f105])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (26454)------------------------------
% 0.20/0.53  % (26454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26454)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (26454)Memory used [KB]: 6524
% 0.20/0.53  % (26454)Time elapsed: 0.114 s
% 0.20/0.53  % (26454)------------------------------
% 0.20/0.53  % (26454)------------------------------
% 0.20/0.53  % (26451)Success in time 0.175 s
%------------------------------------------------------------------------------
