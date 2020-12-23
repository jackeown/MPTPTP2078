%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:12 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 319 expanded)
%              Number of leaves         :   19 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  297 (1179 expanded)
%              Number of equality atoms :  170 (1012 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f106,f187,f226,f229,f260,f270,f289,f310,f326,f345,f357,f412,f444])).

fof(f444,plain,
    ( spl8_4
    | ~ spl8_27 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl8_4
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f14,f15,f395,f55,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f55,plain,
    ( sK0 != sK4
    | spl8_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl8_4
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f395,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_27 ),
    inference(equality_resolution,[],[f356])).

fof(f356,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k2_zfmisc_1(sK4,sK5) = X0 )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl8_27
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k2_zfmisc_1(sK4,sK5) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f15,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

% (26196)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (26212)Refutation not found, incomplete strategy% (26212)------------------------------
% (26212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f412,plain,
    ( spl8_3
    | ~ spl8_27 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl8_3
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f51,f15,f14,f395,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,
    ( sK1 != sK5
    | spl8_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl8_3
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f357,plain,
    ( spl8_9
    | spl8_10
    | spl8_27
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f339,f85,f355,f99,f95])).

fof(f95,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f99,plain,
    ( spl8_10
  <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f85,plain,
    ( spl8_8
  <=> ! [X7,X6] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X6,X7)
        | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f339,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
        | k1_xboole_0 = sK6
        | k2_zfmisc_1(sK4,sK5) = X0 )
    | ~ spl8_8 ),
    inference(superposition,[],[f27,f331])).

fof(f331,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_8 ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X6,X7)
        | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X6 )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f345,plain,
    ( spl8_2
    | ~ spl8_8
    | spl8_9
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl8_2
    | ~ spl8_8
    | spl8_9
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f47,f96,f100,f331,f28])).

fof(f100,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f96,plain,
    ( k1_xboole_0 != sK6
    | spl8_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f47,plain,
    ( sK2 != sK6
    | spl8_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl8_2
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f326,plain,
    ( spl8_13
    | spl8_5
    | spl8_8
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f320,f41,f85,f63,f134])).

fof(f134,plain,
    ( spl8_13
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f63,plain,
    ( spl8_5
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f41,plain,
    ( spl8_1
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f320,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
        | k1_xboole_0 = sK3
        | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0 )
    | ~ spl8_1 ),
    inference(superposition,[],[f27,f272])).

fof(f272,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)
    | ~ spl8_1 ),
    inference(superposition,[],[f30,f42])).

fof(f42,plain,
    ( sK3 = sK7
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f30,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f13,f29,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f13,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f9])).

fof(f310,plain,
    ( ~ spl8_1
    | spl8_12
    | ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl8_1
    | spl8_12
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f17,f131,f294,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f294,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_1
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f293,f36])).

fof(f36,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f293,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_1
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f292,f36])).

fof(f292,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK3)
    | ~ spl8_1
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f291,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f291,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6),sK3)
    | ~ spl8_1
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f290,f42])).

fof(f290,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6),sK7)
    | ~ spl8_17 ),
    inference(superposition,[],[f30,f174])).

fof(f174,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl8_17
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f131,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_12
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f17,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f289,plain,
    ( ~ spl8_1
    | spl8_12
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl8_1
    | spl8_12
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f17,f131,f276,f18])).

fof(f276,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f275,f36])).

fof(f275,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f274,f36])).

fof(f274,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK3)
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f273,f36])).

fof(f273,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6),sK3)
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f272,f178])).

fof(f178,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl8_18
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f270,plain,
    ( spl8_1
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl8_1
    | spl8_12 ),
    inference(unit_resulting_resolution,[],[f43,f17,f30,f131,f28])).

fof(f43,plain,
    ( sK3 != sK7
    | spl8_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f260,plain,(
    ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f16,f15,f14,f132,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f132,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f16,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f229,plain,(
    ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f17,f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f226,plain,
    ( spl8_12
    | spl8_13
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f209,f95,f134,f130])).

fof(f209,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_9 ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_9 ),
    inference(superposition,[],[f18,f200])).

fof(f200,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f199,f36])).

fof(f199,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f198,f35])).

fof(f198,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0),sK7)
    | ~ spl8_9 ),
    inference(superposition,[],[f30,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f187,plain,
    ( spl8_18
    | spl8_17
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f168,f99,f172,f176])).

fof(f168,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl8_10 ),
    inference(trivial_inequality_removal,[],[f167])).

fof(f167,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl8_10 ),
    inference(superposition,[],[f18,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( spl8_10
    | spl8_9
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f92,f63,f95,f99])).

fof(f92,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_5 ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_5 ),
    inference(superposition,[],[f18,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f56,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f12,f53,f49,f45,f41])).

fof(f12,plain,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:07:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (26191)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (26199)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (26208)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (26195)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (26215)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (26207)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (26200)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (26200)Refutation not found, incomplete strategy% (26200)------------------------------
% 0.21/0.52  % (26200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26189)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.22/0.52  % (26200)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (26200)Memory used [KB]: 1663
% 1.22/0.52  % (26200)Time elapsed: 0.075 s
% 1.22/0.52  % (26200)------------------------------
% 1.22/0.52  % (26200)------------------------------
% 1.22/0.52  % (26194)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.22/0.52  % (26192)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.53  % (26211)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.22/0.53  % (26205)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.22/0.53  % (26186)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.53  % (26214)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.22/0.53  % (26190)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.53  % (26203)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.22/0.54  % (26188)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.54  % (26215)Refutation not found, incomplete strategy% (26215)------------------------------
% 1.22/0.54  % (26215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.54  % (26215)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.54  
% 1.22/0.54  % (26215)Memory used [KB]: 1663
% 1.22/0.54  % (26215)Time elapsed: 0.139 s
% 1.22/0.54  % (26215)------------------------------
% 1.22/0.54  % (26215)------------------------------
% 1.22/0.54  % (26206)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.54  % (26187)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.54  % (26198)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.55  % (26204)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.55  % (26197)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.55  % (26199)Refutation found. Thanks to Tanya!
% 1.39/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.55  % (26212)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f446,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(avatar_sat_refutation,[],[f56,f106,f187,f226,f229,f260,f270,f289,f310,f326,f345,f357,f412,f444])).
% 1.39/0.55  fof(f444,plain,(
% 1.39/0.55    spl8_4 | ~spl8_27),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f442])).
% 1.39/0.55  fof(f442,plain,(
% 1.39/0.55    $false | (spl8_4 | ~spl8_27)),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f14,f15,f395,f55,f27])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X0 = X2) )),
% 1.39/0.55    inference(cnf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,plain,(
% 1.39/0.55    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.39/0.55    inference(flattening,[],[f10])).
% 1.39/0.55  fof(f10,plain,(
% 1.39/0.55    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.39/0.55    inference(ennf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.39/0.55  fof(f55,plain,(
% 1.39/0.55    sK0 != sK4 | spl8_4),
% 1.39/0.55    inference(avatar_component_clause,[],[f53])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    spl8_4 <=> sK0 = sK4),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.39/0.55  fof(f395,plain,(
% 1.39/0.55    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl8_27),
% 1.39/0.55    inference(equality_resolution,[],[f356])).
% 1.39/0.55  fof(f356,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k2_zfmisc_1(sK4,sK5) = X0) ) | ~spl8_27),
% 1.39/0.55    inference(avatar_component_clause,[],[f355])).
% 1.39/0.55  fof(f355,plain,(
% 1.39/0.55    spl8_27 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k2_zfmisc_1(sK4,sK5) = X0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.39/0.55  fof(f15,plain,(
% 1.39/0.55    k1_xboole_0 != sK1),
% 1.39/0.55    inference(cnf_transformation,[],[f9])).
% 1.39/0.55  fof(f9,plain,(
% 1.39/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.39/0.55    inference(flattening,[],[f8])).
% 1.39/0.55  fof(f8,plain,(
% 1.39/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.39/0.55    inference(ennf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    inference(negated_conjecture,[],[f6])).
% 1.39/0.55  fof(f6,conjecture,(
% 1.39/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).
% 1.39/0.55  % (26196)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.55  % (26212)Refutation not found, incomplete strategy% (26212)------------------------------
% 1.39/0.55  % (26212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  fof(f14,plain,(
% 1.39/0.56    k1_xboole_0 != sK0),
% 1.39/0.56    inference(cnf_transformation,[],[f9])).
% 1.39/0.56  fof(f412,plain,(
% 1.39/0.56    spl8_3 | ~spl8_27),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f398])).
% 1.39/0.56  fof(f398,plain,(
% 1.39/0.56    $false | (spl8_3 | ~spl8_27)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f51,f15,f14,f395,f28])).
% 1.39/0.56  fof(f28,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X1 = X3) )),
% 1.39/0.56    inference(cnf_transformation,[],[f11])).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    sK1 != sK5 | spl8_3),
% 1.39/0.56    inference(avatar_component_clause,[],[f49])).
% 1.39/0.56  fof(f49,plain,(
% 1.39/0.56    spl8_3 <=> sK1 = sK5),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.39/0.56  fof(f357,plain,(
% 1.39/0.56    spl8_9 | spl8_10 | spl8_27 | ~spl8_8),
% 1.39/0.56    inference(avatar_split_clause,[],[f339,f85,f355,f99,f95])).
% 1.39/0.56  fof(f95,plain,(
% 1.39/0.56    spl8_9 <=> k1_xboole_0 = sK6),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.39/0.56  fof(f99,plain,(
% 1.39/0.56    spl8_10 <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.39/0.56  fof(f85,plain,(
% 1.39/0.56    spl8_8 <=> ! [X7,X6] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X6,X7) | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X6)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.39/0.56  fof(f339,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | k1_xboole_0 = sK6 | k2_zfmisc_1(sK4,sK5) = X0) ) | ~spl8_8),
% 1.39/0.56    inference(superposition,[],[f27,f331])).
% 1.39/0.56  fof(f331,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl8_8),
% 1.39/0.56    inference(equality_resolution,[],[f86])).
% 1.39/0.56  fof(f86,plain,(
% 1.39/0.56    ( ! [X6,X7] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X6,X7) | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X6) ) | ~spl8_8),
% 1.39/0.56    inference(avatar_component_clause,[],[f85])).
% 1.39/0.56  fof(f345,plain,(
% 1.39/0.56    spl8_2 | ~spl8_8 | spl8_9 | spl8_10),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f334])).
% 1.39/0.56  fof(f334,plain,(
% 1.39/0.56    $false | (spl8_2 | ~spl8_8 | spl8_9 | spl8_10)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f47,f96,f100,f331,f28])).
% 1.39/0.56  fof(f100,plain,(
% 1.39/0.56    k1_xboole_0 != k2_zfmisc_1(sK4,sK5) | spl8_10),
% 1.39/0.56    inference(avatar_component_clause,[],[f99])).
% 1.39/0.56  fof(f96,plain,(
% 1.39/0.56    k1_xboole_0 != sK6 | spl8_9),
% 1.39/0.56    inference(avatar_component_clause,[],[f95])).
% 1.39/0.56  fof(f47,plain,(
% 1.39/0.56    sK2 != sK6 | spl8_2),
% 1.39/0.56    inference(avatar_component_clause,[],[f45])).
% 1.39/0.56  fof(f45,plain,(
% 1.39/0.56    spl8_2 <=> sK2 = sK6),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.39/0.56  fof(f326,plain,(
% 1.39/0.56    spl8_13 | spl8_5 | spl8_8 | ~spl8_1),
% 1.39/0.56    inference(avatar_split_clause,[],[f320,f41,f85,f63,f134])).
% 1.39/0.56  fof(f134,plain,(
% 1.39/0.56    spl8_13 <=> k1_xboole_0 = sK3),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.39/0.56  fof(f63,plain,(
% 1.39/0.56    spl8_5 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.39/0.56  fof(f41,plain,(
% 1.39/0.56    spl8_1 <=> sK3 = sK7),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.39/0.56  fof(f320,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | k1_xboole_0 = sK3 | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0) ) | ~spl8_1),
% 1.39/0.56    inference(superposition,[],[f27,f272])).
% 1.39/0.56  fof(f272,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) | ~spl8_1),
% 1.39/0.56    inference(superposition,[],[f30,f42])).
% 1.39/0.56  fof(f42,plain,(
% 1.39/0.56    sK3 = sK7 | ~spl8_1),
% 1.39/0.56    inference(avatar_component_clause,[],[f41])).
% 1.39/0.56  fof(f30,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 1.39/0.56    inference(definition_unfolding,[],[f13,f29,f29])).
% 1.39/0.56  fof(f29,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.39/0.56    inference(definition_unfolding,[],[f26,f21])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f3])).
% 1.39/0.56  fof(f3,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.39/0.56  fof(f26,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f4])).
% 1.39/0.56  fof(f4,axiom,(
% 1.39/0.56    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.39/0.56  fof(f13,plain,(
% 1.39/0.56    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.39/0.56    inference(cnf_transformation,[],[f9])).
% 1.39/0.56  fof(f310,plain,(
% 1.39/0.56    ~spl8_1 | spl8_12 | ~spl8_17),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f299])).
% 1.39/0.56  fof(f299,plain,(
% 1.39/0.56    $false | (~spl8_1 | spl8_12 | ~spl8_17)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f17,f131,f294,f18])).
% 1.39/0.56  fof(f18,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.39/0.56    inference(cnf_transformation,[],[f1])).
% 1.39/0.56  fof(f1,axiom,(
% 1.39/0.56    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.56  fof(f294,plain,(
% 1.39/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | (~spl8_1 | ~spl8_17)),
% 1.39/0.56    inference(forward_demodulation,[],[f293,f36])).
% 1.39/0.56  fof(f36,plain,(
% 1.39/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.56    inference(equality_resolution,[],[f19])).
% 1.39/0.56  fof(f19,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.39/0.56    inference(cnf_transformation,[],[f1])).
% 1.39/0.56  fof(f293,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK3) | (~spl8_1 | ~spl8_17)),
% 1.39/0.56    inference(forward_demodulation,[],[f292,f36])).
% 1.39/0.56  fof(f292,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK3) | (~spl8_1 | ~spl8_17)),
% 1.39/0.56    inference(forward_demodulation,[],[f291,f35])).
% 1.39/0.56  fof(f35,plain,(
% 1.39/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.56    inference(equality_resolution,[],[f20])).
% 1.39/0.56  fof(f20,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.39/0.56    inference(cnf_transformation,[],[f1])).
% 1.39/0.56  fof(f291,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6),sK3) | (~spl8_1 | ~spl8_17)),
% 1.39/0.56    inference(forward_demodulation,[],[f290,f42])).
% 1.39/0.56  fof(f290,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6),sK7) | ~spl8_17),
% 1.39/0.56    inference(superposition,[],[f30,f174])).
% 1.39/0.56  fof(f174,plain,(
% 1.39/0.56    k1_xboole_0 = sK5 | ~spl8_17),
% 1.39/0.56    inference(avatar_component_clause,[],[f172])).
% 1.39/0.56  fof(f172,plain,(
% 1.39/0.56    spl8_17 <=> k1_xboole_0 = sK5),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.39/0.56  fof(f131,plain,(
% 1.39/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | spl8_12),
% 1.39/0.56    inference(avatar_component_clause,[],[f130])).
% 1.39/0.56  fof(f130,plain,(
% 1.39/0.56    spl8_12 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.39/0.56  fof(f17,plain,(
% 1.39/0.56    k1_xboole_0 != sK3),
% 1.39/0.56    inference(cnf_transformation,[],[f9])).
% 1.39/0.56  fof(f289,plain,(
% 1.39/0.56    ~spl8_1 | spl8_12 | ~spl8_18),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f278])).
% 1.39/0.56  fof(f278,plain,(
% 1.39/0.56    $false | (~spl8_1 | spl8_12 | ~spl8_18)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f17,f131,f276,f18])).
% 1.39/0.56  fof(f276,plain,(
% 1.39/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | (~spl8_1 | ~spl8_18)),
% 1.39/0.56    inference(forward_demodulation,[],[f275,f36])).
% 1.39/0.56  fof(f275,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK3) | (~spl8_1 | ~spl8_18)),
% 1.39/0.56    inference(forward_demodulation,[],[f274,f36])).
% 1.39/0.56  fof(f274,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK3) | (~spl8_1 | ~spl8_18)),
% 1.39/0.56    inference(forward_demodulation,[],[f273,f36])).
% 1.39/0.56  fof(f273,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6),sK3) | (~spl8_1 | ~spl8_18)),
% 1.39/0.56    inference(forward_demodulation,[],[f272,f178])).
% 1.39/0.56  fof(f178,plain,(
% 1.39/0.56    k1_xboole_0 = sK4 | ~spl8_18),
% 1.39/0.56    inference(avatar_component_clause,[],[f176])).
% 1.39/0.56  fof(f176,plain,(
% 1.39/0.56    spl8_18 <=> k1_xboole_0 = sK4),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.39/0.56  fof(f270,plain,(
% 1.39/0.56    spl8_1 | spl8_12),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f269])).
% 1.39/0.56  fof(f269,plain,(
% 1.39/0.56    $false | (spl8_1 | spl8_12)),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f43,f17,f30,f131,f28])).
% 1.39/0.56  fof(f43,plain,(
% 1.39/0.56    sK3 != sK7 | spl8_1),
% 1.39/0.56    inference(avatar_component_clause,[],[f41])).
% 1.39/0.56  fof(f260,plain,(
% 1.39/0.56    ~spl8_12),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f249])).
% 1.39/0.56  fof(f249,plain,(
% 1.39/0.56    $false | ~spl8_12),
% 1.39/0.56    inference(unit_resulting_resolution,[],[f16,f15,f14,f132,f34])).
% 1.39/0.56  fof(f34,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.39/0.56    inference(definition_unfolding,[],[f22,f21])).
% 1.39/0.56  fof(f22,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.39/0.56    inference(cnf_transformation,[],[f5])).
% 1.39/0.56  fof(f5,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.39/0.56  fof(f132,plain,(
% 1.39/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_12),
% 1.39/0.56    inference(avatar_component_clause,[],[f130])).
% 1.39/0.56  fof(f16,plain,(
% 1.39/0.56    k1_xboole_0 != sK2),
% 1.39/0.56    inference(cnf_transformation,[],[f9])).
% 1.39/0.56  fof(f229,plain,(
% 1.39/0.56    ~spl8_13),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f227])).
% 1.39/0.56  fof(f227,plain,(
% 1.39/0.56    $false | ~spl8_13),
% 1.39/0.56    inference(subsumption_resolution,[],[f17,f136])).
% 1.39/0.56  fof(f136,plain,(
% 1.39/0.56    k1_xboole_0 = sK3 | ~spl8_13),
% 1.39/0.56    inference(avatar_component_clause,[],[f134])).
% 1.39/0.56  fof(f226,plain,(
% 1.39/0.56    spl8_12 | spl8_13 | ~spl8_9),
% 1.39/0.56    inference(avatar_split_clause,[],[f209,f95,f134,f130])).
% 1.39/0.56  fof(f209,plain,(
% 1.39/0.56    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_9),
% 1.39/0.56    inference(trivial_inequality_removal,[],[f208])).
% 1.39/0.56  fof(f208,plain,(
% 1.39/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_9),
% 1.39/0.56    inference(superposition,[],[f18,f200])).
% 1.39/0.56  fof(f200,plain,(
% 1.39/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_9),
% 1.39/0.56    inference(forward_demodulation,[],[f199,f36])).
% 1.39/0.56  fof(f199,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_9),
% 1.39/0.56    inference(forward_demodulation,[],[f198,f35])).
% 1.39/0.56  fof(f198,plain,(
% 1.39/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0),sK7) | ~spl8_9),
% 1.39/0.56    inference(superposition,[],[f30,f97])).
% 1.39/0.56  fof(f97,plain,(
% 1.39/0.56    k1_xboole_0 = sK6 | ~spl8_9),
% 1.39/0.56    inference(avatar_component_clause,[],[f95])).
% 1.39/0.56  fof(f187,plain,(
% 1.39/0.56    spl8_18 | spl8_17 | ~spl8_10),
% 1.39/0.56    inference(avatar_split_clause,[],[f168,f99,f172,f176])).
% 1.39/0.56  fof(f168,plain,(
% 1.39/0.56    k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | ~spl8_10),
% 1.39/0.56    inference(trivial_inequality_removal,[],[f167])).
% 1.39/0.56  fof(f167,plain,(
% 1.39/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | ~spl8_10),
% 1.39/0.56    inference(superposition,[],[f18,f101])).
% 1.39/0.56  fof(f101,plain,(
% 1.39/0.56    k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl8_10),
% 1.39/0.56    inference(avatar_component_clause,[],[f99])).
% 1.39/0.56  fof(f106,plain,(
% 1.39/0.56    spl8_10 | spl8_9 | ~spl8_5),
% 1.39/0.56    inference(avatar_split_clause,[],[f92,f63,f95,f99])).
% 1.39/0.56  fof(f92,plain,(
% 1.39/0.56    k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl8_5),
% 1.39/0.56    inference(trivial_inequality_removal,[],[f91])).
% 1.39/0.56  fof(f91,plain,(
% 1.39/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl8_5),
% 1.39/0.56    inference(superposition,[],[f18,f65])).
% 1.39/0.56  fof(f65,plain,(
% 1.39/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl8_5),
% 1.39/0.56    inference(avatar_component_clause,[],[f63])).
% 1.39/0.56  fof(f56,plain,(
% 1.39/0.56    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 1.39/0.56    inference(avatar_split_clause,[],[f12,f53,f49,f45,f41])).
% 1.39/0.56  fof(f12,plain,(
% 1.39/0.56    sK0 != sK4 | sK1 != sK5 | sK2 != sK6 | sK3 != sK7),
% 1.39/0.56    inference(cnf_transformation,[],[f9])).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (26199)------------------------------
% 1.39/0.56  % (26199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (26199)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (26199)Memory used [KB]: 6396
% 1.39/0.56  % (26199)Time elapsed: 0.143 s
% 1.39/0.56  % (26199)------------------------------
% 1.39/0.56  % (26199)------------------------------
% 1.39/0.56  % (26210)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.56  % (26212)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (26212)Memory used [KB]: 6268
% 1.39/0.56  % (26212)Time elapsed: 0.141 s
% 1.39/0.56  % (26212)------------------------------
% 1.39/0.56  % (26212)------------------------------
% 1.39/0.56  % (26185)Success in time 0.191 s
%------------------------------------------------------------------------------
