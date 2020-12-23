%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 123 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  217 ( 344 expanded)
%              Number of equality atoms :   36 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f60,f72,f76,f83,f88,f102,f107,f111,f125,f134,f144,f153])).

fof(f153,plain,
    ( ~ spl4_1
    | ~ spl4_12
    | spl4_20
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_12
    | spl4_20
    | ~ spl4_23 ),
    inference(unit_resulting_resolution,[],[f33,f124,f143,f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | k1_xboole_0 = k7_relat_1(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f143,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_23
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f124,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_20
  <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f33,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f144,plain,
    ( spl4_23
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f135,f132,f44,f142])).

fof(f44,plain,
    ( spl4_4
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f132,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X0)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f135,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(resolution,[],[f133,f45])).

fof(f45,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl4_21
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f117,f109,f58,f132])).

fof(f58,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK3(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f109,plain,
    ( spl4_18
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_xboole_0(X0,X2)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X0)
        | r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(resolution,[],[f110,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_xboole_0(X0,X2)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f109])).

fof(f125,plain,
    ( ~ spl4_20
    | ~ spl4_2
    | ~ spl4_10
    | spl4_17 ),
    inference(avatar_split_clause,[],[f113,f105,f70,f36,f123])).

fof(f36,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f70,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f105,plain,
    ( spl4_17
  <=> k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f113,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_10
    | spl4_17 ),
    inference(subsumption_resolution,[],[f112,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f112,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ spl4_10
    | spl4_17 ),
    inference(superposition,[],[f106,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f106,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f105])).

fof(f111,plain,
    ( spl4_18
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f78,f74,f58,f109])).

fof(f74,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_xboole_0(X0,X2)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(resolution,[],[f75,f59])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f107,plain,
    ( ~ spl4_17
    | spl4_3
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f103,f100,f40,f105])).

fof(f40,plain,
    ( spl4_3
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f100,plain,
    ( spl4_16
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f103,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | spl4_3
    | ~ spl4_16 ),
    inference(superposition,[],[f41,f101])).

fof(f101,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f41,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f102,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f89,f86,f32,f100])).

fof(f86,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f89,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(resolution,[],[f87,f33])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f29,f86])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f83,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f22,f81])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f76,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f23,f74])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f72,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f60,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f30,f44])).

fof(f30,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f42,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f38,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (31354)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.42  % (31354)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f157,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f60,f72,f76,f83,f88,f102,f107,f111,f125,f134,f144,f153])).
% 0.21/0.42  fof(f153,plain,(
% 0.21/0.42    ~spl4_1 | ~spl4_12 | spl4_20 | ~spl4_23),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f147])).
% 0.21/0.42  fof(f147,plain,(
% 0.21/0.42    $false | (~spl4_1 | ~spl4_12 | spl4_20 | ~spl4_23)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f33,f124,f143,f82])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1)) ) | ~spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f81])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    spl4_12 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f143,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl4_23),
% 0.21/0.42    inference(avatar_component_clause,[],[f142])).
% 0.21/0.42  fof(f142,plain,(
% 0.21/0.42    spl4_23 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0) | spl4_20),
% 0.21/0.42    inference(avatar_component_clause,[],[f123])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    spl4_20 <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    v1_relat_1(sK2) | ~spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl4_1 <=> v1_relat_1(sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f144,plain,(
% 0.21/0.42    spl4_23 | ~spl4_4 | ~spl4_21),
% 0.21/0.42    inference(avatar_split_clause,[],[f135,f132,f44,f142])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl4_4 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    spl4_21 <=> ! [X1,X0] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_21)),
% 0.21/0.42    inference(resolution,[],[f133,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f44])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) ) | ~spl4_21),
% 0.21/0.42    inference(avatar_component_clause,[],[f132])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    spl4_21 | ~spl4_7 | ~spl4_18),
% 0.21/0.42    inference(avatar_split_clause,[],[f117,f109,f58,f132])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    spl4_18 <=> ! [X1,X0,X2] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) ) | (~spl4_7 | ~spl4_18)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f114])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) ) | (~spl4_7 | ~spl4_18)),
% 0.21/0.42    inference(resolution,[],[f110,f59])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1)) ) | ~spl4_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f109])).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    ~spl4_20 | ~spl4_2 | ~spl4_10 | spl4_17),
% 0.21/0.42    inference(avatar_split_clause,[],[f113,f105,f70,f36,f123])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl4_2 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl4_10 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    spl4_17 <=> k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0) | (~spl4_2 | ~spl4_10 | spl4_17)),
% 0.21/0.42    inference(subsumption_resolution,[],[f112,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f36])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0) | ~r1_xboole_0(sK0,sK1) | (~spl4_10 | spl4_17)),
% 0.21/0.42    inference(superposition,[],[f106,f71])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f70])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | spl4_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f105])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    spl4_18 | ~spl4_7 | ~spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f78,f74,f58,f109])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl4_11 <=> ! [X1,X0,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1)) ) | (~spl4_7 | ~spl4_11)),
% 0.21/0.42    inference(resolution,[],[f75,f59])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) ) | ~spl4_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f74])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    ~spl4_17 | spl4_3 | ~spl4_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f103,f100,f40,f105])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl4_3 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    spl4_16 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | (spl4_3 | ~spl4_16)),
% 0.21/0.42    inference(superposition,[],[f41,f101])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | ~spl4_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f100])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f40])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    spl4_16 | ~spl4_1 | ~spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f89,f86,f32,f100])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    spl4_13 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | (~spl4_1 | ~spl4_13)),
% 0.21/0.42    inference(resolution,[],[f87,f33])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) ) | ~spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f86])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f86])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f81])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f74])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(rectify,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f70])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f44])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.42    inference(equality_resolution,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ~spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f40])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f36])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f32])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    v1_relat_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (31354)------------------------------
% 0.21/0.42  % (31354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (31354)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (31354)Memory used [KB]: 10618
% 0.21/0.42  % (31354)Time elapsed: 0.008 s
% 0.21/0.42  % (31354)------------------------------
% 0.21/0.42  % (31354)------------------------------
% 0.21/0.42  % (31344)Success in time 0.067 s
%------------------------------------------------------------------------------
