%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:13 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 368 expanded)
%              Number of leaves         :   42 ( 156 expanded)
%              Depth                    :    8
%              Number of atoms          :  420 ( 996 expanded)
%              Number of equality atoms :   82 ( 239 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f67,f72,f93,f100,f105,f112,f117,f129,f143,f145,f152,f157,f164,f169,f173,f181,f206,f208,f223,f254,f262,f269,f274,f282,f288,f295,f300,f313,f322,f328,f329,f352,f353])).

fof(f353,plain,
    ( spl9_13
    | spl9_31
    | ~ spl9_32 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl9_13
    | spl9_31
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f116,f299,f303,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( r1_tarski(X1,X3)
          | ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            & ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f303,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl9_32
  <=> r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f299,plain,
    ( ~ r1_tarski(sK4,sK0)
    | spl9_31 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl9_31
  <=> r1_tarski(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK5)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_13
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f352,plain,
    ( spl9_12
    | spl9_30
    | ~ spl9_32 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl9_12
    | spl9_30
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f111,f294,f303,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f294,plain,
    ( ~ r1_tarski(sK5,sK1)
    | spl9_30 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl9_30
  <=> r1_tarski(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f111,plain,
    ( ~ v1_xboole_0(sK4)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl9_12
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f329,plain,
    ( spl9_10
    | spl9_32
    | ~ spl9_35 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl9_10
    | spl9_32
    | ~ spl9_35 ),
    inference(unit_resulting_resolution,[],[f99,f304,f320,f30])).

fof(f320,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl9_35
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f304,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1))
    | spl9_32 ),
    inference(avatar_component_clause,[],[f302])).

fof(f99,plain,
    ( ~ v1_xboole_0(sK6)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl9_10
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f328,plain,
    ( spl9_11
    | spl9_26
    | ~ spl9_35 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl9_11
    | spl9_26
    | ~ spl9_35 ),
    inference(unit_resulting_resolution,[],[f268,f104,f320,f29])).

fof(f104,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK4,sK5))
    | spl9_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl9_11
  <=> v1_xboole_0(k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f268,plain,
    ( ~ r1_tarski(sK6,sK2)
    | spl9_26 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl9_26
  <=> r1_tarski(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f322,plain,
    ( spl9_35
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f315,f311,f318])).

fof(f311,plain,
    ( spl9_34
  <=> ! [X5,X4] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X4,X5))
        | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f315,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_34 ),
    inference(resolution,[],[f312,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f312,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X4,X5))
        | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),X4) )
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f311])).

fof(f313,plain,
    ( spl9_20
    | spl9_34
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f232,f203,f311,f161])).

fof(f161,plain,
    ( spl9_20
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f203,plain,
    ( spl9_23
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

% (32757)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f232,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X4,X5))
        | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),X4)
        | v1_xboole_0(sK3) )
    | ~ spl9_23 ),
    inference(superposition,[],[f30,f205])).

fof(f205,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f300,plain,
    ( ~ spl9_31
    | spl9_2
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f290,f285,f52,f297])).

fof(f52,plain,
    ( spl9_2
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f285,plain,
    ( spl9_29
  <=> r1_tarski(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f290,plain,
    ( sK0 = sK4
    | ~ r1_tarski(sK4,sK0)
    | ~ spl9_29 ),
    inference(resolution,[],[f287,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f287,plain,
    ( r1_tarski(sK0,sK4)
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f285])).

% (32756)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f295,plain,
    ( ~ spl9_30
    | spl9_3
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f283,f279,f56,f292])).

fof(f56,plain,
    ( spl9_3
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f279,plain,
    ( spl9_28
  <=> r1_tarski(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f283,plain,
    ( sK1 = sK5
    | ~ r1_tarski(sK5,sK1)
    | ~ spl9_28 ),
    inference(resolution,[],[f281,f37])).

fof(f281,plain,
    ( r1_tarski(sK1,sK5)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f279])).

fof(f288,plain,
    ( spl9_19
    | spl9_29
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f276,f271,f285,f154])).

fof(f154,plain,
    ( spl9_19
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f271,plain,
    ( spl9_27
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f276,plain,
    ( r1_tarski(sK0,sK4)
    | v1_xboole_0(sK1)
    | ~ spl9_27 ),
    inference(resolution,[],[f273,f30])).

fof(f273,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f271])).

fof(f282,plain,
    ( spl9_18
    | spl9_28
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f275,f271,f279,f149])).

fof(f149,plain,
    ( spl9_18
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f275,plain,
    ( r1_tarski(sK1,sK5)
    | v1_xboole_0(sK0)
    | ~ spl9_27 ),
    inference(resolution,[],[f273,f29])).

fof(f274,plain,
    ( spl9_17
    | spl9_27
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f256,f251,f271,f136])).

fof(f136,plain,
    ( spl9_17
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f251,plain,
    ( spl9_24
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f256,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | v1_xboole_0(sK2)
    | ~ spl9_24 ),
    inference(resolution,[],[f253,f30])).

fof(f253,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f251])).

fof(f269,plain,
    ( ~ spl9_26
    | spl9_4
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f263,f259,f60,f266])).

fof(f60,plain,
    ( spl9_4
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f259,plain,
    ( spl9_25
  <=> r1_tarski(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f263,plain,
    ( sK2 = sK6
    | ~ r1_tarski(sK6,sK2)
    | ~ spl9_25 ),
    inference(resolution,[],[f261,f37])).

fof(f261,plain,
    ( r1_tarski(sK2,sK6)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f259])).

fof(f262,plain,
    ( spl9_16
    | spl9_25
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f255,f251,f259,f132])).

fof(f132,plain,
    ( spl9_16
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f255,plain,
    ( r1_tarski(sK2,sK6)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl9_24 ),
    inference(resolution,[],[f253,f29])).

fof(f254,plain,
    ( spl9_20
    | spl9_24
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f247,f69,f251,f161])).

fof(f69,plain,
    ( spl9_6
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f247,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | v1_xboole_0(sK3)
    | ~ spl9_6 ),
    inference(resolution,[],[f76,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(k2_zfmisc_1(X6,X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
        | r1_tarski(X6,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
        | v1_xboole_0(X7) )
    | ~ spl9_6 ),
    inference(superposition,[],[f30,f71])).

fof(f71,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f223,plain,
    ( spl9_8
    | ~ spl9_14 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl9_8
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f86,f124,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f124,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl9_14
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f86,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | spl9_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl9_8
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f208,plain,
    ( spl9_21
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f191,f171,f166])).

fof(f166,plain,
    ( spl9_21
  <=> r1_tarski(sK7,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f171,plain,
    ( spl9_22
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X0,X1))
        | r1_tarski(sK7,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f191,plain,
    ( r1_tarski(sK7,sK3)
    | ~ spl9_22 ),
    inference(resolution,[],[f172,f44])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X0,X1))
        | r1_tarski(sK7,X1) )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f171])).

fof(f206,plain,
    ( spl9_23
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f199,f69,f64,f203])).

fof(f64,plain,
    ( spl9_5
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f199,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f71,f65])).

fof(f65,plain,
    ( sK3 = sK7
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f181,plain,
    ( spl9_1
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl9_1
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f49,f87,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f87,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f49,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl9_1
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f173,plain,
    ( spl9_9
    | spl9_22
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f73,f69,f171,f90])).

fof(f90,plain,
    ( spl9_9
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X0,X1))
        | r1_tarski(sK7,X1)
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) )
    | ~ spl9_6 ),
    inference(superposition,[],[f29,f71])).

fof(f169,plain,
    ( ~ spl9_21
    | spl9_5
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f140,f126,f64,f166])).

fof(f126,plain,
    ( spl9_15
  <=> r1_tarski(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f140,plain,
    ( sK3 = sK7
    | ~ r1_tarski(sK7,sK3)
    | ~ spl9_15 ),
    inference(resolution,[],[f128,f37])).

fof(f128,plain,
    ( r1_tarski(sK3,sK7)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f126])).

fof(f164,plain,
    ( ~ spl9_20
    | spl9_8 ),
    inference(avatar_split_clause,[],[f159,f85,f161])).

fof(f159,plain,
    ( ~ v1_xboole_0(sK3)
    | spl9_8 ),
    inference(resolution,[],[f86,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f157,plain,
    ( ~ spl9_19
    | spl9_16 ),
    inference(avatar_split_clause,[],[f147,f132,f154])).

fof(f147,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_16 ),
    inference(resolution,[],[f133,f32])).

fof(f133,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl9_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f152,plain,
    ( ~ spl9_18
    | spl9_16 ),
    inference(avatar_split_clause,[],[f146,f132,f149])).

fof(f146,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_16 ),
    inference(resolution,[],[f133,f33])).

fof(f145,plain,
    ( ~ spl9_16
    | spl9_14 ),
    inference(avatar_split_clause,[],[f141,f122,f132])).

fof(f141,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl9_14 ),
    inference(resolution,[],[f123,f33])).

fof(f123,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl9_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f143,plain,
    ( ~ spl9_17
    | spl9_14 ),
    inference(avatar_split_clause,[],[f142,f122,f136])).

fof(f142,plain,
    ( ~ v1_xboole_0(sK2)
    | spl9_14 ),
    inference(resolution,[],[f123,f32])).

fof(f129,plain,
    ( spl9_14
    | spl9_15
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f118,f69,f126,f122])).

fof(f118,plain,
    ( r1_tarski(sK3,sK7)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_6 ),
    inference(resolution,[],[f74,f45])).

fof(f74,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
        | r1_tarski(X3,sK7)
        | v1_xboole_0(X2) )
    | ~ spl9_6 ),
    inference(superposition,[],[f29,f71])).

fof(f117,plain,
    ( ~ spl9_13
    | spl9_11 ),
    inference(avatar_split_clause,[],[f107,f102,f114])).

fof(f107,plain,
    ( ~ v1_xboole_0(sK5)
    | spl9_11 ),
    inference(resolution,[],[f104,f32])).

fof(f112,plain,
    ( ~ spl9_12
    | spl9_11 ),
    inference(avatar_split_clause,[],[f106,f102,f109])).

fof(f106,plain,
    ( ~ v1_xboole_0(sK4)
    | spl9_11 ),
    inference(resolution,[],[f104,f33])).

fof(f105,plain,
    ( ~ spl9_11
    | spl9_9 ),
    inference(avatar_split_clause,[],[f94,f90,f102])).

fof(f94,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK4,sK5))
    | spl9_9 ),
    inference(resolution,[],[f92,f33])).

fof(f92,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl9_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f100,plain,
    ( ~ spl9_10
    | spl9_9 ),
    inference(avatar_split_clause,[],[f95,f90,f97])).

fof(f95,plain,
    ( ~ v1_xboole_0(sK6)
    | spl9_9 ),
    inference(resolution,[],[f92,f32])).

fof(f93,plain,
    ( ~ spl9_9
    | spl9_8
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f78,f69,f85,f90])).

fof(f78,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl9_6 ),
    inference(superposition,[],[f33,f71])).

fof(f72,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f43,f69])).

fof(f43,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f26,f41,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f26,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f67,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f28,f64,f60,f56,f52])).

fof(f28,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f42,f47])).

fof(f42,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f27,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:17:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (32753)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (32758)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (32751)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (32751)Refutation not found, incomplete strategy% (32751)------------------------------
% 0.20/0.50  % (32751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (306)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (307)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (32752)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (32751)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32751)Memory used [KB]: 1663
% 0.20/0.51  % (32751)Time elapsed: 0.096 s
% 0.20/0.51  % (32751)------------------------------
% 0.20/0.51  % (32751)------------------------------
% 0.20/0.51  % (311)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (32761)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (32759)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (32766)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (32763)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (32754)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (311)Refutation not found, incomplete strategy% (311)------------------------------
% 0.20/0.52  % (311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (311)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (311)Memory used [KB]: 1663
% 0.20/0.52  % (311)Time elapsed: 0.107 s
% 0.20/0.52  % (311)------------------------------
% 0.20/0.52  % (311)------------------------------
% 0.20/0.52  % (310)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (32750)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (32762)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (32760)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (302)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (309)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (32755)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.53  % (301)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.53  % (32762)Refutation not found, incomplete strategy% (32762)------------------------------
% 1.31/0.53  % (32762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (305)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.54  % (32766)Refutation not found, incomplete strategy% (32766)------------------------------
% 1.31/0.54  % (32766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (32766)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (32766)Memory used [KB]: 10618
% 1.31/0.54  % (32766)Time elapsed: 0.124 s
% 1.31/0.54  % (32766)------------------------------
% 1.31/0.54  % (32766)------------------------------
% 1.31/0.54  % (308)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.54  % (308)Refutation not found, incomplete strategy% (308)------------------------------
% 1.31/0.54  % (308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (308)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (308)Memory used [KB]: 6268
% 1.31/0.54  % (308)Time elapsed: 0.130 s
% 1.31/0.54  % (308)------------------------------
% 1.31/0.54  % (308)------------------------------
% 1.31/0.54  % (300)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.54  % (303)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.54  % (32762)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (32762)Memory used [KB]: 10618
% 1.31/0.54  % (32762)Time elapsed: 0.137 s
% 1.31/0.54  % (32762)------------------------------
% 1.31/0.54  % (32762)------------------------------
% 1.31/0.54  % (32765)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.54  % (304)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.55  % (32760)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.31/0.55  % (32764)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.31/0.55  % (300)Refutation not found, incomplete strategy% (300)------------------------------
% 1.31/0.55  % (300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (300)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (300)Memory used [KB]: 1663
% 1.31/0.55  % (300)Time elapsed: 0.142 s
% 1.31/0.55  % (300)------------------------------
% 1.31/0.55  % (300)------------------------------
% 1.31/0.55  % SZS output start Proof for theBenchmark
% 1.31/0.55  fof(f354,plain,(
% 1.31/0.55    $false),
% 1.31/0.55    inference(avatar_sat_refutation,[],[f50,f67,f72,f93,f100,f105,f112,f117,f129,f143,f145,f152,f157,f164,f169,f173,f181,f206,f208,f223,f254,f262,f269,f274,f282,f288,f295,f300,f313,f322,f328,f329,f352,f353])).
% 1.31/0.55  fof(f353,plain,(
% 1.31/0.55    spl9_13 | spl9_31 | ~spl9_32),
% 1.31/0.55    inference(avatar_contradiction_clause,[],[f348])).
% 1.31/0.55  fof(f348,plain,(
% 1.31/0.55    $false | (spl9_13 | spl9_31 | ~spl9_32)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f116,f299,f303,f30])).
% 1.31/0.55  fof(f30,plain,(
% 1.31/0.55    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(X1,X3) | v1_xboole_0(X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f14])).
% 1.31/0.55  fof(f14,plain,(
% 1.31/0.55    ! [X0] : (! [X1,X2,X3] : (r1_tarski(X1,X3) | (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) & ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) | v1_xboole_0(X0))),
% 1.31/0.55    inference(ennf_transformation,[],[f6])).
% 1.31/0.55  fof(f6,axiom,(
% 1.31/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 1.31/0.55  fof(f303,plain,(
% 1.31/0.55    r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1)) | ~spl9_32),
% 1.31/0.55    inference(avatar_component_clause,[],[f302])).
% 1.31/0.55  fof(f302,plain,(
% 1.31/0.55    spl9_32 <=> r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1))),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 1.31/0.55  fof(f299,plain,(
% 1.31/0.55    ~r1_tarski(sK4,sK0) | spl9_31),
% 1.31/0.55    inference(avatar_component_clause,[],[f297])).
% 1.31/0.55  fof(f297,plain,(
% 1.31/0.55    spl9_31 <=> r1_tarski(sK4,sK0)),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 1.31/0.55  fof(f116,plain,(
% 1.31/0.55    ~v1_xboole_0(sK5) | spl9_13),
% 1.31/0.55    inference(avatar_component_clause,[],[f114])).
% 1.31/0.55  fof(f114,plain,(
% 1.31/0.55    spl9_13 <=> v1_xboole_0(sK5)),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.31/0.55  fof(f352,plain,(
% 1.31/0.55    spl9_12 | spl9_30 | ~spl9_32),
% 1.31/0.55    inference(avatar_contradiction_clause,[],[f347])).
% 1.31/0.55  fof(f347,plain,(
% 1.31/0.55    $false | (spl9_12 | spl9_30 | ~spl9_32)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f111,f294,f303,f29])).
% 1.31/0.55  fof(f29,plain,(
% 1.31/0.55    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | r1_tarski(X1,X3) | v1_xboole_0(X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f14])).
% 1.31/0.55  fof(f294,plain,(
% 1.31/0.55    ~r1_tarski(sK5,sK1) | spl9_30),
% 1.31/0.55    inference(avatar_component_clause,[],[f292])).
% 1.31/0.55  fof(f292,plain,(
% 1.31/0.55    spl9_30 <=> r1_tarski(sK5,sK1)),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 1.31/0.55  fof(f111,plain,(
% 1.31/0.55    ~v1_xboole_0(sK4) | spl9_12),
% 1.31/0.55    inference(avatar_component_clause,[],[f109])).
% 1.31/0.55  fof(f109,plain,(
% 1.31/0.55    spl9_12 <=> v1_xboole_0(sK4)),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.31/0.55  fof(f329,plain,(
% 1.31/0.55    spl9_10 | spl9_32 | ~spl9_35),
% 1.31/0.55    inference(avatar_contradiction_clause,[],[f324])).
% 1.31/0.55  fof(f324,plain,(
% 1.31/0.55    $false | (spl9_10 | spl9_32 | ~spl9_35)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f99,f304,f320,f30])).
% 1.31/0.55  fof(f320,plain,(
% 1.31/0.55    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_35),
% 1.31/0.55    inference(avatar_component_clause,[],[f318])).
% 1.31/0.55  fof(f318,plain,(
% 1.31/0.55    spl9_35 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 1.31/0.55  fof(f304,plain,(
% 1.31/0.55    ~r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1)) | spl9_32),
% 1.31/0.55    inference(avatar_component_clause,[],[f302])).
% 1.31/0.55  fof(f99,plain,(
% 1.31/0.55    ~v1_xboole_0(sK6) | spl9_10),
% 1.31/0.55    inference(avatar_component_clause,[],[f97])).
% 1.31/0.55  fof(f97,plain,(
% 1.31/0.55    spl9_10 <=> v1_xboole_0(sK6)),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.31/0.55  fof(f328,plain,(
% 1.31/0.55    spl9_11 | spl9_26 | ~spl9_35),
% 1.31/0.55    inference(avatar_contradiction_clause,[],[f323])).
% 1.31/0.55  fof(f323,plain,(
% 1.31/0.55    $false | (spl9_11 | spl9_26 | ~spl9_35)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f268,f104,f320,f29])).
% 1.31/0.55  fof(f104,plain,(
% 1.31/0.55    ~v1_xboole_0(k2_zfmisc_1(sK4,sK5)) | spl9_11),
% 1.31/0.55    inference(avatar_component_clause,[],[f102])).
% 1.31/0.55  fof(f102,plain,(
% 1.31/0.55    spl9_11 <=> v1_xboole_0(k2_zfmisc_1(sK4,sK5))),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.31/0.55  fof(f268,plain,(
% 1.31/0.55    ~r1_tarski(sK6,sK2) | spl9_26),
% 1.31/0.55    inference(avatar_component_clause,[],[f266])).
% 1.31/0.55  fof(f266,plain,(
% 1.31/0.55    spl9_26 <=> r1_tarski(sK6,sK2)),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.31/0.55  fof(f322,plain,(
% 1.31/0.55    spl9_35 | ~spl9_34),
% 1.31/0.55    inference(avatar_split_clause,[],[f315,f311,f318])).
% 1.31/0.55  fof(f311,plain,(
% 1.31/0.55    spl9_34 <=> ! [X5,X4] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X4,X5)) | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),X4))),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 1.31/0.55  fof(f315,plain,(
% 1.31/0.55    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_34),
% 1.31/0.55    inference(resolution,[],[f312,f44])).
% 1.31/0.55  fof(f44,plain,(
% 1.31/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.55    inference(equality_resolution,[],[f36])).
% 1.31/0.55  fof(f36,plain,(
% 1.31/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.55    inference(cnf_transformation,[],[f23])).
% 1.31/0.55  fof(f23,plain,(
% 1.31/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.55    inference(flattening,[],[f22])).
% 1.31/0.55  fof(f22,plain,(
% 1.31/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.55    inference(nnf_transformation,[],[f3])).
% 1.31/0.55  fof(f3,axiom,(
% 1.31/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.55  fof(f312,plain,(
% 1.31/0.55    ( ! [X4,X5] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X4,X5)) | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),X4)) ) | ~spl9_34),
% 1.31/0.55    inference(avatar_component_clause,[],[f311])).
% 1.31/0.55  fof(f313,plain,(
% 1.31/0.55    spl9_20 | spl9_34 | ~spl9_23),
% 1.31/0.55    inference(avatar_split_clause,[],[f232,f203,f311,f161])).
% 1.31/0.55  fof(f161,plain,(
% 1.31/0.55    spl9_20 <=> v1_xboole_0(sK3)),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.31/0.55  fof(f203,plain,(
% 1.31/0.55    spl9_23 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 1.50/0.55  % (32757)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.55  fof(f232,plain,(
% 1.50/0.55    ( ! [X4,X5] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X4,X5)) | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),X4) | v1_xboole_0(sK3)) ) | ~spl9_23),
% 1.50/0.55    inference(superposition,[],[f30,f205])).
% 1.50/0.55  fof(f205,plain,(
% 1.50/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) | ~spl9_23),
% 1.50/0.55    inference(avatar_component_clause,[],[f203])).
% 1.50/0.55  fof(f300,plain,(
% 1.50/0.55    ~spl9_31 | spl9_2 | ~spl9_29),
% 1.50/0.55    inference(avatar_split_clause,[],[f290,f285,f52,f297])).
% 1.50/0.55  fof(f52,plain,(
% 1.50/0.55    spl9_2 <=> sK0 = sK4),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.50/0.55  fof(f285,plain,(
% 1.50/0.55    spl9_29 <=> r1_tarski(sK0,sK4)),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 1.50/0.55  fof(f290,plain,(
% 1.50/0.55    sK0 = sK4 | ~r1_tarski(sK4,sK0) | ~spl9_29),
% 1.50/0.55    inference(resolution,[],[f287,f37])).
% 1.50/0.55  fof(f37,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f23])).
% 1.50/0.55  fof(f287,plain,(
% 1.50/0.55    r1_tarski(sK0,sK4) | ~spl9_29),
% 1.50/0.55    inference(avatar_component_clause,[],[f285])).
% 1.50/0.56  % (32756)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.56  fof(f295,plain,(
% 1.50/0.56    ~spl9_30 | spl9_3 | ~spl9_28),
% 1.50/0.56    inference(avatar_split_clause,[],[f283,f279,f56,f292])).
% 1.50/0.56  fof(f56,plain,(
% 1.50/0.56    spl9_3 <=> sK1 = sK5),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.50/0.56  fof(f279,plain,(
% 1.50/0.56    spl9_28 <=> r1_tarski(sK1,sK5)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 1.50/0.56  fof(f283,plain,(
% 1.50/0.56    sK1 = sK5 | ~r1_tarski(sK5,sK1) | ~spl9_28),
% 1.50/0.56    inference(resolution,[],[f281,f37])).
% 1.50/0.56  fof(f281,plain,(
% 1.50/0.56    r1_tarski(sK1,sK5) | ~spl9_28),
% 1.50/0.56    inference(avatar_component_clause,[],[f279])).
% 1.50/0.56  fof(f288,plain,(
% 1.50/0.56    spl9_19 | spl9_29 | ~spl9_27),
% 1.50/0.56    inference(avatar_split_clause,[],[f276,f271,f285,f154])).
% 1.50/0.56  fof(f154,plain,(
% 1.50/0.56    spl9_19 <=> v1_xboole_0(sK1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 1.50/0.56  fof(f271,plain,(
% 1.50/0.56    spl9_27 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 1.50/0.56  fof(f276,plain,(
% 1.50/0.56    r1_tarski(sK0,sK4) | v1_xboole_0(sK1) | ~spl9_27),
% 1.50/0.56    inference(resolution,[],[f273,f30])).
% 1.50/0.56  fof(f273,plain,(
% 1.50/0.56    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | ~spl9_27),
% 1.50/0.56    inference(avatar_component_clause,[],[f271])).
% 1.50/0.56  fof(f282,plain,(
% 1.50/0.56    spl9_18 | spl9_28 | ~spl9_27),
% 1.50/0.56    inference(avatar_split_clause,[],[f275,f271,f279,f149])).
% 1.50/0.56  fof(f149,plain,(
% 1.50/0.56    spl9_18 <=> v1_xboole_0(sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.50/0.56  fof(f275,plain,(
% 1.50/0.56    r1_tarski(sK1,sK5) | v1_xboole_0(sK0) | ~spl9_27),
% 1.50/0.56    inference(resolution,[],[f273,f29])).
% 1.50/0.56  fof(f274,plain,(
% 1.50/0.56    spl9_17 | spl9_27 | ~spl9_24),
% 1.50/0.56    inference(avatar_split_clause,[],[f256,f251,f271,f136])).
% 1.50/0.56  fof(f136,plain,(
% 1.50/0.56    spl9_17 <=> v1_xboole_0(sK2)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.50/0.56  fof(f251,plain,(
% 1.50/0.56    spl9_24 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 1.50/0.56  fof(f256,plain,(
% 1.50/0.56    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | v1_xboole_0(sK2) | ~spl9_24),
% 1.50/0.56    inference(resolution,[],[f253,f30])).
% 1.50/0.56  fof(f253,plain,(
% 1.50/0.56    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl9_24),
% 1.50/0.56    inference(avatar_component_clause,[],[f251])).
% 1.50/0.56  fof(f269,plain,(
% 1.50/0.56    ~spl9_26 | spl9_4 | ~spl9_25),
% 1.50/0.56    inference(avatar_split_clause,[],[f263,f259,f60,f266])).
% 1.50/0.56  fof(f60,plain,(
% 1.50/0.56    spl9_4 <=> sK2 = sK6),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.50/0.56  fof(f259,plain,(
% 1.50/0.56    spl9_25 <=> r1_tarski(sK2,sK6)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 1.50/0.56  fof(f263,plain,(
% 1.50/0.56    sK2 = sK6 | ~r1_tarski(sK6,sK2) | ~spl9_25),
% 1.50/0.56    inference(resolution,[],[f261,f37])).
% 1.50/0.56  fof(f261,plain,(
% 1.50/0.56    r1_tarski(sK2,sK6) | ~spl9_25),
% 1.50/0.56    inference(avatar_component_clause,[],[f259])).
% 1.50/0.56  fof(f262,plain,(
% 1.50/0.56    spl9_16 | spl9_25 | ~spl9_24),
% 1.50/0.56    inference(avatar_split_clause,[],[f255,f251,f259,f132])).
% 1.50/0.56  fof(f132,plain,(
% 1.50/0.56    spl9_16 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.50/0.56  fof(f255,plain,(
% 1.50/0.56    r1_tarski(sK2,sK6) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl9_24),
% 1.50/0.56    inference(resolution,[],[f253,f29])).
% 1.50/0.56  fof(f254,plain,(
% 1.50/0.56    spl9_20 | spl9_24 | ~spl9_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f247,f69,f251,f161])).
% 1.50/0.56  fof(f69,plain,(
% 1.50/0.56    spl9_6 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.50/0.56  fof(f247,plain,(
% 1.50/0.56    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | v1_xboole_0(sK3) | ~spl9_6),
% 1.50/0.56    inference(resolution,[],[f76,f45])).
% 1.50/0.56  fof(f45,plain,(
% 1.50/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.56    inference(equality_resolution,[],[f35])).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f23])).
% 1.50/0.56  fof(f76,plain,(
% 1.50/0.56    ( ! [X6,X7] : (~r1_tarski(k2_zfmisc_1(X6,X7),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | r1_tarski(X6,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | v1_xboole_0(X7)) ) | ~spl9_6),
% 1.50/0.56    inference(superposition,[],[f30,f71])).
% 1.50/0.56  fof(f71,plain,(
% 1.50/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) | ~spl9_6),
% 1.50/0.56    inference(avatar_component_clause,[],[f69])).
% 1.50/0.56  fof(f223,plain,(
% 1.50/0.56    spl9_8 | ~spl9_14),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f221])).
% 1.50/0.56  fof(f221,plain,(
% 1.50/0.56    $false | (spl9_8 | ~spl9_14)),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f86,f124,f33])).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.50/0.56  fof(f124,plain,(
% 1.50/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_14),
% 1.50/0.56    inference(avatar_component_clause,[],[f122])).
% 1.50/0.56  fof(f122,plain,(
% 1.50/0.56    spl9_14 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.50/0.56  fof(f86,plain,(
% 1.50/0.56    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | spl9_8),
% 1.50/0.56    inference(avatar_component_clause,[],[f85])).
% 1.50/0.56  fof(f85,plain,(
% 1.50/0.56    spl9_8 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.50/0.56  fof(f208,plain,(
% 1.50/0.56    spl9_21 | ~spl9_22),
% 1.50/0.56    inference(avatar_split_clause,[],[f191,f171,f166])).
% 1.50/0.56  fof(f166,plain,(
% 1.50/0.56    spl9_21 <=> r1_tarski(sK7,sK3)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.50/0.56  fof(f171,plain,(
% 1.50/0.56    spl9_22 <=> ! [X1,X0] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X0,X1)) | r1_tarski(sK7,X1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 1.50/0.56  fof(f191,plain,(
% 1.50/0.56    r1_tarski(sK7,sK3) | ~spl9_22),
% 1.50/0.56    inference(resolution,[],[f172,f44])).
% 1.50/0.56  fof(f172,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X0,X1)) | r1_tarski(sK7,X1)) ) | ~spl9_22),
% 1.50/0.56    inference(avatar_component_clause,[],[f171])).
% 1.50/0.56  fof(f206,plain,(
% 1.50/0.56    spl9_23 | ~spl9_5 | ~spl9_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f199,f69,f64,f203])).
% 1.50/0.56  fof(f64,plain,(
% 1.50/0.56    spl9_5 <=> sK3 = sK7),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.50/0.56  fof(f199,plain,(
% 1.50/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) | (~spl9_5 | ~spl9_6)),
% 1.50/0.56    inference(backward_demodulation,[],[f71,f65])).
% 1.50/0.56  fof(f65,plain,(
% 1.50/0.56    sK3 = sK7 | ~spl9_5),
% 1.50/0.56    inference(avatar_component_clause,[],[f64])).
% 1.50/0.56  fof(f181,plain,(
% 1.50/0.56    spl9_1 | ~spl9_8),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f178])).
% 1.50/0.56  fof(f178,plain,(
% 1.50/0.56    $false | (spl9_1 | ~spl9_8)),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f49,f87,f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f15])).
% 1.50/0.56  fof(f15,plain,(
% 1.50/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.50/0.56  fof(f87,plain,(
% 1.50/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl9_8),
% 1.50/0.56    inference(avatar_component_clause,[],[f85])).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | spl9_1),
% 1.50/0.56    inference(avatar_component_clause,[],[f47])).
% 1.50/0.56  fof(f47,plain,(
% 1.50/0.56    spl9_1 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.50/0.56  fof(f173,plain,(
% 1.50/0.56    spl9_9 | spl9_22 | ~spl9_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f73,f69,f171,f90])).
% 1.50/0.56  fof(f90,plain,(
% 1.50/0.56    spl9_9 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.50/0.56  fof(f73,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X0,X1)) | r1_tarski(sK7,X1) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))) ) | ~spl9_6),
% 1.50/0.56    inference(superposition,[],[f29,f71])).
% 1.50/0.56  fof(f169,plain,(
% 1.50/0.56    ~spl9_21 | spl9_5 | ~spl9_15),
% 1.50/0.56    inference(avatar_split_clause,[],[f140,f126,f64,f166])).
% 1.50/0.56  fof(f126,plain,(
% 1.50/0.56    spl9_15 <=> r1_tarski(sK3,sK7)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.50/0.56  fof(f140,plain,(
% 1.50/0.56    sK3 = sK7 | ~r1_tarski(sK7,sK3) | ~spl9_15),
% 1.50/0.56    inference(resolution,[],[f128,f37])).
% 1.50/0.56  fof(f128,plain,(
% 1.50/0.56    r1_tarski(sK3,sK7) | ~spl9_15),
% 1.50/0.56    inference(avatar_component_clause,[],[f126])).
% 1.50/0.56  fof(f164,plain,(
% 1.50/0.56    ~spl9_20 | spl9_8),
% 1.50/0.56    inference(avatar_split_clause,[],[f159,f85,f161])).
% 1.50/0.56  fof(f159,plain,(
% 1.50/0.56    ~v1_xboole_0(sK3) | spl9_8),
% 1.50/0.56    inference(resolution,[],[f86,f32])).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f16,plain,(
% 1.50/0.56    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.50/0.56  fof(f157,plain,(
% 1.50/0.56    ~spl9_19 | spl9_16),
% 1.50/0.56    inference(avatar_split_clause,[],[f147,f132,f154])).
% 1.50/0.56  fof(f147,plain,(
% 1.50/0.56    ~v1_xboole_0(sK1) | spl9_16),
% 1.50/0.56    inference(resolution,[],[f133,f32])).
% 1.50/0.56  fof(f133,plain,(
% 1.50/0.56    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl9_16),
% 1.50/0.56    inference(avatar_component_clause,[],[f132])).
% 1.50/0.56  fof(f152,plain,(
% 1.50/0.56    ~spl9_18 | spl9_16),
% 1.50/0.56    inference(avatar_split_clause,[],[f146,f132,f149])).
% 1.50/0.56  fof(f146,plain,(
% 1.50/0.56    ~v1_xboole_0(sK0) | spl9_16),
% 1.50/0.56    inference(resolution,[],[f133,f33])).
% 1.50/0.56  fof(f145,plain,(
% 1.50/0.56    ~spl9_16 | spl9_14),
% 1.50/0.56    inference(avatar_split_clause,[],[f141,f122,f132])).
% 1.50/0.56  fof(f141,plain,(
% 1.50/0.56    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl9_14),
% 1.50/0.56    inference(resolution,[],[f123,f33])).
% 1.50/0.56  fof(f123,plain,(
% 1.50/0.56    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl9_14),
% 1.50/0.56    inference(avatar_component_clause,[],[f122])).
% 1.50/0.56  fof(f143,plain,(
% 1.50/0.56    ~spl9_17 | spl9_14),
% 1.50/0.56    inference(avatar_split_clause,[],[f142,f122,f136])).
% 1.50/0.56  fof(f142,plain,(
% 1.50/0.56    ~v1_xboole_0(sK2) | spl9_14),
% 1.50/0.56    inference(resolution,[],[f123,f32])).
% 1.50/0.56  fof(f129,plain,(
% 1.50/0.56    spl9_14 | spl9_15 | ~spl9_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f118,f69,f126,f122])).
% 1.50/0.56  fof(f118,plain,(
% 1.50/0.56    r1_tarski(sK3,sK7) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_6),
% 1.50/0.56    inference(resolution,[],[f74,f45])).
% 1.50/0.56  fof(f74,plain,(
% 1.50/0.56    ( ! [X2,X3] : (~r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | r1_tarski(X3,sK7) | v1_xboole_0(X2)) ) | ~spl9_6),
% 1.50/0.56    inference(superposition,[],[f29,f71])).
% 1.50/0.56  fof(f117,plain,(
% 1.50/0.56    ~spl9_13 | spl9_11),
% 1.50/0.56    inference(avatar_split_clause,[],[f107,f102,f114])).
% 1.50/0.56  fof(f107,plain,(
% 1.50/0.56    ~v1_xboole_0(sK5) | spl9_11),
% 1.50/0.56    inference(resolution,[],[f104,f32])).
% 1.50/0.56  fof(f112,plain,(
% 1.50/0.56    ~spl9_12 | spl9_11),
% 1.50/0.56    inference(avatar_split_clause,[],[f106,f102,f109])).
% 1.50/0.56  fof(f106,plain,(
% 1.50/0.56    ~v1_xboole_0(sK4) | spl9_11),
% 1.50/0.56    inference(resolution,[],[f104,f33])).
% 1.50/0.56  fof(f105,plain,(
% 1.50/0.56    ~spl9_11 | spl9_9),
% 1.50/0.56    inference(avatar_split_clause,[],[f94,f90,f102])).
% 1.50/0.56  fof(f94,plain,(
% 1.50/0.56    ~v1_xboole_0(k2_zfmisc_1(sK4,sK5)) | spl9_9),
% 1.50/0.56    inference(resolution,[],[f92,f33])).
% 1.50/0.56  fof(f92,plain,(
% 1.50/0.56    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl9_9),
% 1.50/0.56    inference(avatar_component_clause,[],[f90])).
% 1.50/0.56  fof(f100,plain,(
% 1.50/0.56    ~spl9_10 | spl9_9),
% 1.50/0.56    inference(avatar_split_clause,[],[f95,f90,f97])).
% 1.50/0.56  fof(f95,plain,(
% 1.50/0.56    ~v1_xboole_0(sK6) | spl9_9),
% 1.50/0.56    inference(resolution,[],[f92,f32])).
% 1.50/0.56  fof(f93,plain,(
% 1.50/0.56    ~spl9_9 | spl9_8 | ~spl9_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f78,f69,f85,f90])).
% 1.50/0.56  fof(f78,plain,(
% 1.50/0.56    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl9_6),
% 1.50/0.56    inference(superposition,[],[f33,f71])).
% 1.50/0.56  fof(f72,plain,(
% 1.50/0.56    spl9_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f43,f69])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 1.50/0.56    inference(definition_unfolding,[],[f26,f41,f41])).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.50/0.56    inference(definition_unfolding,[],[f39,f38])).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f8])).
% 1.50/0.56  fof(f8,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f9])).
% 1.50/0.56  fof(f9,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.50/0.56    inference(cnf_transformation,[],[f21])).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f20])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f13,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.50/0.56    inference(flattening,[],[f12])).
% 1.50/0.56  fof(f12,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.50/0.56    inference(ennf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.50/0.56    inference(negated_conjecture,[],[f10])).
% 1.50/0.56  fof(f10,conjecture,(
% 1.50/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).
% 1.50/0.56  fof(f67,plain,(
% 1.50/0.56    ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5),
% 1.50/0.56    inference(avatar_split_clause,[],[f28,f64,f60,f56,f52])).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 1.50/0.56    inference(cnf_transformation,[],[f21])).
% 1.50/0.56  fof(f50,plain,(
% 1.50/0.56    ~spl9_1),
% 1.50/0.56    inference(avatar_split_clause,[],[f42,f47])).
% 1.50/0.56  fof(f42,plain,(
% 1.50/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 1.50/0.56    inference(definition_unfolding,[],[f27,f41])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 1.50/0.56    inference(cnf_transformation,[],[f21])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (32760)------------------------------
% 1.50/0.56  % (32760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (32760)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (32760)Memory used [KB]: 10874
% 1.50/0.56  % (32760)Time elapsed: 0.152 s
% 1.50/0.56  % (32760)------------------------------
% 1.50/0.56  % (32760)------------------------------
% 1.50/0.56  % (32749)Success in time 0.198 s
%------------------------------------------------------------------------------
