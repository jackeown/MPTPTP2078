%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 331 expanded)
%              Number of leaves         :   42 ( 153 expanded)
%              Depth                    :    8
%              Number of atoms          :  580 (1801 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f94,f99,f104,f114,f124,f134,f175,f177,f179,f186,f192,f198,f260,f339,f353,f396,f401,f422,f436,f441,f445,f487,f494,f592])).

fof(f592,plain,
    ( ~ spl8_37
    | ~ spl8_43
    | spl8_47 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | ~ spl8_37
    | ~ spl8_43
    | spl8_47 ),
    inference(subsumption_resolution,[],[f582,f525])).

fof(f525,plain,
    ( ! [X0] : sP0(X0,sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f440,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f440,plain,
    ( r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl8_43
  <=> r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f582,plain,
    ( ~ sP0(u1_struct_0(sK4),sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl8_37
    | spl8_47 ),
    inference(unit_resulting_resolution,[],[f352,f484,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP0(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP0(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f484,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK4))
    | spl8_47 ),
    inference(avatar_component_clause,[],[f482])).

fof(f482,plain,
    ( spl8_47
  <=> r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f352,plain,
    ( sP1(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl8_37
  <=> sP1(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f494,plain,
    ( ~ spl8_47
    | ~ spl8_38
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f475,f433,f393,f482])).

fof(f393,plain,
    ( spl8_38
  <=> r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f433,plain,
    ( spl8_42
  <=> r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f475,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK4))
    | ~ spl8_38
    | ~ spl8_42 ),
    inference(resolution,[],[f435,f402])).

fof(f402,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK5))
        | ~ r2_hidden(X0,u1_struct_0(sK4)) )
    | ~ spl8_38 ),
    inference(resolution,[],[f395,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f395,plain,
    ( r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f393])).

fof(f435,plain,
    ( r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK5))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f433])).

fof(f487,plain,
    ( ~ spl8_47
    | ~ spl8_39
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f469,f433,f398,f482])).

fof(f398,plain,
    ( spl8_39
  <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f469,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK4))
    | ~ spl8_39
    | ~ spl8_42 ),
    inference(unit_resulting_resolution,[],[f400,f435,f62])).

fof(f400,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f398])).

fof(f445,plain,
    ( ~ spl8_4
    | spl8_3
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f211,f195,f189,f87,f91])).

fof(f91,plain,
    ( spl8_4
  <=> r1_tsep_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f87,plain,
    ( spl8_3
  <=> r1_tsep_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f189,plain,
    ( spl8_20
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f195,plain,
    ( spl8_21
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f211,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | spl8_3
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f191,f197,f89,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f89,plain,
    ( ~ r1_tsep_1(sK3,sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f197,plain,
    ( l1_struct_0(sK3)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f195])).

fof(f191,plain,
    ( l1_struct_0(sK5)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f189])).

fof(f441,plain,
    ( spl8_43
    | spl8_40 ),
    inference(avatar_split_clause,[],[f429,f419,f438])).

fof(f419,plain,
    ( spl8_40
  <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f429,plain,
    ( r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3))
    | spl8_40 ),
    inference(unit_resulting_resolution,[],[f421,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f421,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | spl8_40 ),
    inference(avatar_component_clause,[],[f419])).

fof(f436,plain,
    ( spl8_42
    | spl8_40 ),
    inference(avatar_split_clause,[],[f430,f419,f433])).

fof(f430,plain,
    ( r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK5))
    | spl8_40 ),
    inference(unit_resulting_resolution,[],[f421,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f422,plain,
    ( ~ spl8_40
    | spl8_4
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f411,f195,f189,f91,f419])).

fof(f411,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | spl8_4
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f191,f197,f93,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

% (8306)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f93,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f401,plain,
    ( spl8_39
    | ~ spl8_2
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f389,f189,f183,f82,f398])).

fof(f82,plain,
    ( spl8_2
  <=> r1_tsep_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f183,plain,
    ( spl8_19
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f389,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ spl8_2
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f191,f185,f84,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f185,plain,
    ( l1_struct_0(sK4)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f396,plain,
    ( spl8_38
    | ~ spl8_1
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f390,f189,f183,f78,f393])).

fof(f78,plain,
    ( spl8_1
  <=> r1_tsep_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f390,plain,
    ( r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ spl8_1
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f185,f191,f80,f55])).

fof(f80,plain,
    ( r1_tsep_1(sK4,sK5)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f353,plain,
    ( spl8_37
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f341,f335,f350])).

fof(f335,plain,
    ( spl8_35
  <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f341,plain,
    ( sP1(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f337,f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f76,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f24,f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f337,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f335])).

fof(f339,plain,
    ( spl8_35
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f333,f257,f335])).

fof(f257,plain,
    ( spl8_25
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f333,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl8_25 ),
    inference(resolution,[],[f259,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f259,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f257])).

fof(f260,plain,
    ( spl8_25
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f236,f159,f96,f257])).

fof(f96,plain,
    ( spl8_5
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f159,plain,
    ( spl8_16
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f236,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f161,f98,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f98,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f161,plain,
    ( l1_pre_topc(sK4)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f198,plain,
    ( spl8_21
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f193,f169,f195])).

fof(f169,plain,
    ( spl8_18
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f193,plain,
    ( l1_struct_0(sK3)
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f171,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f171,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f192,plain,
    ( spl8_20
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f187,f164,f189])).

fof(f164,plain,
    ( spl8_17
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f187,plain,
    ( l1_struct_0(sK5)
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f166,f57])).

fof(f166,plain,
    ( l1_pre_topc(sK5)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f164])).

fof(f186,plain,
    ( spl8_19
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f181,f159,f183])).

fof(f181,plain,
    ( l1_struct_0(sK4)
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f161,f57])).

fof(f179,plain,
    ( spl8_16
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f178,f131,f111,f159])).

fof(f111,plain,
    ( spl8_8
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f131,plain,
    ( spl8_12
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f178,plain,
    ( l1_pre_topc(sK4)
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f157,f133])).

fof(f133,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f157,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f58,f113])).

fof(f113,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f177,plain,
    ( spl8_17
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f176,f131,f101,f164])).

fof(f101,plain,
    ( spl8_6
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f176,plain,
    ( l1_pre_topc(sK5)
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f156,f133])).

fof(f156,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ spl8_6 ),
    inference(resolution,[],[f58,f103])).

fof(f103,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f175,plain,
    ( spl8_18
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f174,f131,f121,f169])).

fof(f121,plain,
    ( spl8_10
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f174,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f155,f133])).

fof(f155,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f58,f123])).

fof(f123,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f134,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f45,f131])).

fof(f45,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( r1_tsep_1(sK5,sK4)
      | r1_tsep_1(sK4,sK5) )
    & ( ~ r1_tsep_1(sK5,sK3)
      | ~ r1_tsep_1(sK3,sK5) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

% (8315)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK3)
                | ~ r1_tsep_1(sK3,X3) )
              & m1_pre_topc(sK3,X2)
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK3)
              | ~ r1_tsep_1(sK3,X3) )
            & m1_pre_topc(sK3,X2)
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK4)
            | r1_tsep_1(sK4,X3) )
          & ( ~ r1_tsep_1(X3,sK3)
            | ~ r1_tsep_1(sK3,X3) )
          & m1_pre_topc(sK3,sK4)
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK4)
          | r1_tsep_1(sK4,X3) )
        & ( ~ r1_tsep_1(X3,sK3)
          | ~ r1_tsep_1(sK3,X3) )
        & m1_pre_topc(sK3,sK4)
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ( r1_tsep_1(sK5,sK4)
        | r1_tsep_1(sK4,sK5) )
      & ( ~ r1_tsep_1(sK5,sK3)
        | ~ r1_tsep_1(sK3,sK5) )
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f124,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f47,f121])).

fof(f47,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f49,f111])).

fof(f49,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f104,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f51,f101])).

fof(f51,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f99,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f52,f96])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f53,f91,f87])).

fof(f53,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f54,f82,f78])).

fof(f54,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (8303)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (8302)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (8313)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (8305)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (8298)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8300)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (8311)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (8317)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (8297)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (8299)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (8309)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8314)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (8317)Refutation not found, incomplete strategy% (8317)------------------------------
% 0.21/0.51  % (8317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8317)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8317)Memory used [KB]: 10618
% 0.21/0.51  % (8317)Time elapsed: 0.060 s
% 0.21/0.51  % (8317)------------------------------
% 0.21/0.51  % (8317)------------------------------
% 0.21/0.51  % (8304)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (8301)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (8308)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (8313)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f593,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f85,f94,f99,f104,f114,f124,f134,f175,f177,f179,f186,f192,f198,f260,f339,f353,f396,f401,f422,f436,f441,f445,f487,f494,f592])).
% 0.21/0.52  fof(f592,plain,(
% 0.21/0.52    ~spl8_37 | ~spl8_43 | spl8_47),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f591])).
% 0.21/0.52  fof(f591,plain,(
% 0.21/0.52    $false | (~spl8_37 | ~spl8_43 | spl8_47)),
% 0.21/0.52    inference(subsumption_resolution,[],[f582,f525])).
% 0.21/0.52  fof(f525,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(X0,sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3))) ) | ~spl8_43),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f440,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP0(X1,X3,X0)))),
% 0.21/0.52    inference(flattening,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f440,plain,(
% 0.21/0.52    r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3)) | ~spl8_43),
% 0.21/0.52    inference(avatar_component_clause,[],[f438])).
% 0.21/0.52  fof(f438,plain,(
% 0.21/0.52    spl8_43 <=> r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.21/0.52  fof(f582,plain,(
% 0.21/0.52    ~sP0(u1_struct_0(sK4),sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3)) | (~spl8_37 | spl8_47)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f352,f484,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f484,plain,(
% 0.21/0.52    ~r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK4)) | spl8_47),
% 0.21/0.52    inference(avatar_component_clause,[],[f482])).
% 0.21/0.52  fof(f482,plain,(
% 0.21/0.52    spl8_47 <=> r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    sP1(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK4)) | ~spl8_37),
% 0.21/0.52    inference(avatar_component_clause,[],[f350])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    spl8_37 <=> sP1(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.21/0.52  fof(f494,plain,(
% 0.21/0.52    ~spl8_47 | ~spl8_38 | ~spl8_42),
% 0.21/0.52    inference(avatar_split_clause,[],[f475,f433,f393,f482])).
% 0.21/0.52  fof(f393,plain,(
% 0.21/0.52    spl8_38 <=> r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.21/0.52  fof(f433,plain,(
% 0.21/0.52    spl8_42 <=> r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    ~r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK4)) | (~spl8_38 | ~spl8_42)),
% 0.21/0.52    inference(resolution,[],[f435,f402])).
% 0.21/0.52  fof(f402,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK5)) | ~r2_hidden(X0,u1_struct_0(sK4))) ) | ~spl8_38),
% 0.21/0.52    inference(resolution,[],[f395,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.52  fof(f395,plain,(
% 0.21/0.52    r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) | ~spl8_38),
% 0.21/0.52    inference(avatar_component_clause,[],[f393])).
% 0.21/0.52  fof(f435,plain,(
% 0.21/0.52    r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK5)) | ~spl8_42),
% 0.21/0.52    inference(avatar_component_clause,[],[f433])).
% 0.21/0.52  fof(f487,plain,(
% 0.21/0.52    ~spl8_47 | ~spl8_39 | ~spl8_42),
% 0.21/0.52    inference(avatar_split_clause,[],[f469,f433,f398,f482])).
% 0.21/0.52  fof(f398,plain,(
% 0.21/0.52    spl8_39 <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.21/0.52  fof(f469,plain,(
% 0.21/0.52    ~r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK4)) | (~spl8_39 | ~spl8_42)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f400,f435,f62])).
% 0.21/0.52  fof(f400,plain,(
% 0.21/0.52    r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) | ~spl8_39),
% 0.21/0.52    inference(avatar_component_clause,[],[f398])).
% 0.21/0.52  fof(f445,plain,(
% 0.21/0.52    ~spl8_4 | spl8_3 | ~spl8_20 | ~spl8_21),
% 0.21/0.52    inference(avatar_split_clause,[],[f211,f195,f189,f87,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl8_4 <=> r1_tsep_1(sK5,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl8_3 <=> r1_tsep_1(sK3,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    spl8_20 <=> l1_struct_0(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    spl8_21 <=> l1_struct_0(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    ~r1_tsep_1(sK5,sK3) | (spl8_3 | ~spl8_20 | ~spl8_21)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f191,f197,f89,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~r1_tsep_1(sK3,sK5) | spl8_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    l1_struct_0(sK3) | ~spl8_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f195])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    l1_struct_0(sK5) | ~spl8_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f189])).
% 0.21/0.52  fof(f441,plain,(
% 0.21/0.52    spl8_43 | spl8_40),
% 0.21/0.52    inference(avatar_split_clause,[],[f429,f419,f438])).
% 0.21/0.52  fof(f419,plain,(
% 0.21/0.52    spl8_40 <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.21/0.52  fof(f429,plain,(
% 0.21/0.52    r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK3)) | spl8_40),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f421,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f421,plain,(
% 0.21/0.52    ~r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) | spl8_40),
% 0.21/0.52    inference(avatar_component_clause,[],[f419])).
% 0.21/0.52  fof(f436,plain,(
% 0.21/0.52    spl8_42 | spl8_40),
% 0.21/0.52    inference(avatar_split_clause,[],[f430,f419,f433])).
% 0.21/0.52  fof(f430,plain,(
% 0.21/0.52    r2_hidden(sK6(u1_struct_0(sK5),u1_struct_0(sK3)),u1_struct_0(sK5)) | spl8_40),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f421,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f422,plain,(
% 0.21/0.52    ~spl8_40 | spl8_4 | ~spl8_20 | ~spl8_21),
% 0.21/0.52    inference(avatar_split_clause,[],[f411,f195,f189,f91,f419])).
% 0.21/0.52  fof(f411,plain,(
% 0.21/0.52    ~r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) | (spl8_4 | ~spl8_20 | ~spl8_21)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f191,f197,f93,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  % (8306)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~r1_tsep_1(sK5,sK3) | spl8_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f401,plain,(
% 0.21/0.52    spl8_39 | ~spl8_2 | ~spl8_19 | ~spl8_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f389,f189,f183,f82,f398])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl8_2 <=> r1_tsep_1(sK5,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl8_19 <=> l1_struct_0(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.52  fof(f389,plain,(
% 0.21/0.52    r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) | (~spl8_2 | ~spl8_19 | ~spl8_20)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f191,f185,f84,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    r1_tsep_1(sK5,sK4) | ~spl8_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    l1_struct_0(sK4) | ~spl8_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f183])).
% 0.21/0.52  fof(f396,plain,(
% 0.21/0.52    spl8_38 | ~spl8_1 | ~spl8_19 | ~spl8_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f390,f189,f183,f78,f393])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl8_1 <=> r1_tsep_1(sK4,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.52  fof(f390,plain,(
% 0.21/0.52    r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) | (~spl8_1 | ~spl8_19 | ~spl8_20)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f185,f191,f80,f55])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    r1_tsep_1(sK4,sK5) | ~spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f353,plain,(
% 0.21/0.52    spl8_37 | ~spl8_35),
% 0.21/0.52    inference(avatar_split_clause,[],[f341,f335,f350])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    spl8_35 <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.21/0.52  fof(f341,plain,(
% 0.21/0.52    sP1(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK4)) | ~spl8_35),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f337,f200])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP1(X0,X1,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(superposition,[],[f76,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP1(X0,X1,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.21/0.52    inference(definition_folding,[],[f1,f24,f23])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.52  fof(f337,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) | ~spl8_35),
% 0.21/0.52    inference(avatar_component_clause,[],[f335])).
% 0.21/0.52  fof(f339,plain,(
% 0.21/0.52    spl8_35 | ~spl8_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f333,f257,f335])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    spl8_25 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) | ~spl8_25),
% 0.21/0.52    inference(resolution,[],[f259,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) | ~spl8_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f257])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    spl8_25 | ~spl8_5 | ~spl8_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f236,f159,f96,f257])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl8_5 <=> m1_pre_topc(sK3,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl8_16 <=> l1_pre_topc(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) | (~spl8_5 | ~spl8_16)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f161,f98,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK4) | ~spl8_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    l1_pre_topc(sK4) | ~spl8_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f159])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    spl8_21 | ~spl8_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f193,f169,f195])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    spl8_18 <=> l1_pre_topc(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    l1_struct_0(sK3) | ~spl8_18),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f171,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    l1_pre_topc(sK3) | ~spl8_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f169])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    spl8_20 | ~spl8_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f187,f164,f189])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    spl8_17 <=> l1_pre_topc(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    l1_struct_0(sK5) | ~spl8_17),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f166,f57])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    l1_pre_topc(sK5) | ~spl8_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f164])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    spl8_19 | ~spl8_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f181,f159,f183])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    l1_struct_0(sK4) | ~spl8_16),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f161,f57])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    spl8_16 | ~spl8_8 | ~spl8_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f178,f131,f111,f159])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl8_8 <=> m1_pre_topc(sK4,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl8_12 <=> l1_pre_topc(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    l1_pre_topc(sK4) | (~spl8_8 | ~spl8_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f157,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    l1_pre_topc(sK2) | ~spl8_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    l1_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~spl8_8),
% 0.21/0.52    inference(resolution,[],[f58,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    m1_pre_topc(sK4,sK2) | ~spl8_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f111])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    spl8_17 | ~spl8_6 | ~spl8_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f176,f131,f101,f164])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl8_6 <=> m1_pre_topc(sK5,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    l1_pre_topc(sK5) | (~spl8_6 | ~spl8_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f156,f133])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    l1_pre_topc(sK5) | ~l1_pre_topc(sK2) | ~spl8_6),
% 0.21/0.52    inference(resolution,[],[f58,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    m1_pre_topc(sK5,sK2) | ~spl8_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    spl8_18 | ~spl8_10 | ~spl8_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f174,f131,f121,f169])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl8_10 <=> m1_pre_topc(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    l1_pre_topc(sK3) | (~spl8_10 | ~spl8_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f155,f133])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    l1_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~spl8_10),
% 0.21/0.52    inference(resolution,[],[f58,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK2) | ~spl8_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl8_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f45,f131])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    l1_pre_topc(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ((((r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & (~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f29,f28,f27,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  % (8315)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : ((r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ? [X3] : ((r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => ((r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & (~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl8_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f121])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl8_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f49,f111])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    m1_pre_topc(sK4,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl8_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f101])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    m1_pre_topc(sK5,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl8_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f52,f96])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~spl8_3 | ~spl8_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f53,f91,f87])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl8_1 | spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f54,f82,f78])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (8313)------------------------------
% 0.21/0.52  % (8313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8313)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (8313)Memory used [KB]: 11001
% 0.21/0.52  % (8313)Time elapsed: 0.085 s
% 0.21/0.52  % (8313)------------------------------
% 0.21/0.52  % (8313)------------------------------
% 0.21/0.52  % (8296)Success in time 0.163 s
%------------------------------------------------------------------------------
