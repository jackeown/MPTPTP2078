%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 164 expanded)
%              Number of leaves         :   32 (  75 expanded)
%              Depth                    :    6
%              Number of atoms          :  298 ( 429 expanded)
%              Number of equality atoms :   35 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f73,f77,f81,f89,f112,f117,f121,f125,f133,f140,f168,f213,f219,f228,f247,f290,f339,f347])).

fof(f347,plain,
    ( ~ spl4_4
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_31
    | ~ spl4_44 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_31
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f232,f345])).

fof(f345,plain,
    ( ! [X0] : k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)
    | ~ spl4_17
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f338,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f131])).

% (23974)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f131,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f338,plain,
    ( ! [X2] : ~ r1_xboole_0(k1_xboole_0,X2)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl4_44
  <=> ! [X2] : ~ r1_xboole_0(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f232,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f230,f76])).

fof(f76,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_4
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f230,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_18
    | ~ spl4_31 ),
    inference(superposition,[],[f139,f227])).

fof(f227,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl4_31
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f139,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_18
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f339,plain,
    ( spl4_44
    | ~ spl4_31
    | ~ spl4_33
    | spl4_38 ),
    inference(avatar_split_clause,[],[f291,f287,f245,f226,f337])).

fof(f245,plain,
    ( spl4_33
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f287,plain,
    ( spl4_38
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f291,plain,
    ( ! [X2] : ~ r1_xboole_0(k1_xboole_0,X2)
    | ~ spl4_31
    | ~ spl4_33
    | spl4_38 ),
    inference(subsumption_resolution,[],[f249,f289])).

fof(f289,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_38 ),
    inference(avatar_component_clause,[],[f287])).

fof(f249,plain,
    ( ! [X2] :
        ( v1_xboole_0(k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,X2) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(superposition,[],[f246,f227])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f245])).

fof(f290,plain,
    ( ~ spl4_38
    | spl4_13
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f222,f216,f114,f287])).

fof(f114,plain,
    ( spl4_13
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f216,plain,
    ( spl4_30
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f222,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_13
    | ~ spl4_30 ),
    inference(superposition,[],[f116,f218])).

fof(f218,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f216])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f247,plain,
    ( spl4_33
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f147,f119,f87,f245])).

fof(f87,plain,
    ( spl4_7
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f119,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k3_xboole_0(X0,X1)) )
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(resolution,[],[f120,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f228,plain,
    ( spl4_31
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f148,f123,f71,f226])).

fof(f71,plain,
    ( spl4_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f123,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f148,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f72,f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f72,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f219,plain,
    ( spl4_30
    | spl4_2
    | ~ spl4_22
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f214,f210,f166,f66,f216])).

fof(f66,plain,
    ( spl4_2
  <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f166,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f210,plain,
    ( spl4_29
  <=> m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f214,plain,
    ( k1_xboole_0 = sK1
    | spl4_2
    | ~ spl4_22
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f178,f212])).

fof(f212,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f210])).

fof(f178,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK0,sK1)
    | spl4_2
    | ~ spl4_22 ),
    inference(resolution,[],[f167,f68])).

fof(f68,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f166])).

fof(f213,plain,
    ( spl4_29
    | ~ spl4_1
    | ~ spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f143,f114,f110,f61,f210])).

fof(f61,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f110,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f143,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_12
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f116,f63,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f63,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f168,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f52,f166])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f140,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f44,f138])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f133,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f54,f131])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f125,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f51,f123])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f121,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f50,f119])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f117,plain,
    ( ~ spl4_13
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f90,f79,f61,f114])).

fof(f79,plain,
    ( spl4_5
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f63,f80])).

fof(f80,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f112,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f46,f110])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f89,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
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

fof(f81,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f41,f79])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f73,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f38,f71])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f69,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f64,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f36,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:39:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (23966)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.43  % (23966)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f351,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f64,f69,f73,f77,f81,f89,f112,f117,f121,f125,f133,f140,f168,f213,f219,f228,f247,f290,f339,f347])).
% 0.22/0.43  fof(f347,plain,(
% 0.22/0.43    ~spl4_4 | ~spl4_17 | ~spl4_18 | ~spl4_31 | ~spl4_44),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f346])).
% 0.22/0.43  fof(f346,plain,(
% 0.22/0.43    $false | (~spl4_4 | ~spl4_17 | ~spl4_18 | ~spl4_31 | ~spl4_44)),
% 0.22/0.43    inference(subsumption_resolution,[],[f232,f345])).
% 0.22/0.43  fof(f345,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)) ) | (~spl4_17 | ~spl4_44)),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f338,f132])).
% 0.22/0.43  fof(f132,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl4_17),
% 0.22/0.43    inference(avatar_component_clause,[],[f131])).
% 0.22/0.43  % (23974)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.43  fof(f131,plain,(
% 0.22/0.43    spl4_17 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.43  fof(f338,plain,(
% 0.22/0.43    ( ! [X2] : (~r1_xboole_0(k1_xboole_0,X2)) ) | ~spl4_44),
% 0.22/0.43    inference(avatar_component_clause,[],[f337])).
% 0.22/0.43  fof(f337,plain,(
% 0.22/0.43    spl4_44 <=> ! [X2] : ~r1_xboole_0(k1_xboole_0,X2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.22/0.43  fof(f232,plain,(
% 0.22/0.43    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) ) | (~spl4_4 | ~spl4_18 | ~spl4_31)),
% 0.22/0.43    inference(forward_demodulation,[],[f230,f76])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f75])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    spl4_4 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.43  fof(f230,plain,(
% 0.22/0.43    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) | (~spl4_18 | ~spl4_31)),
% 0.22/0.43    inference(superposition,[],[f139,f227])).
% 0.22/0.43  fof(f227,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl4_31),
% 0.22/0.43    inference(avatar_component_clause,[],[f226])).
% 0.22/0.43  fof(f226,plain,(
% 0.22/0.43    spl4_31 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.43  fof(f139,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl4_18),
% 0.22/0.43    inference(avatar_component_clause,[],[f138])).
% 0.22/0.43  fof(f138,plain,(
% 0.22/0.43    spl4_18 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.43  fof(f339,plain,(
% 0.22/0.43    spl4_44 | ~spl4_31 | ~spl4_33 | spl4_38),
% 0.22/0.43    inference(avatar_split_clause,[],[f291,f287,f245,f226,f337])).
% 0.22/0.43  fof(f245,plain,(
% 0.22/0.43    spl4_33 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.43  fof(f287,plain,(
% 0.22/0.43    spl4_38 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.22/0.43  fof(f291,plain,(
% 0.22/0.43    ( ! [X2] : (~r1_xboole_0(k1_xboole_0,X2)) ) | (~spl4_31 | ~spl4_33 | spl4_38)),
% 0.22/0.43    inference(subsumption_resolution,[],[f249,f289])).
% 0.22/0.43  fof(f289,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | spl4_38),
% 0.22/0.43    inference(avatar_component_clause,[],[f287])).
% 0.22/0.43  fof(f249,plain,(
% 0.22/0.43    ( ! [X2] : (v1_xboole_0(k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X2)) ) | (~spl4_31 | ~spl4_33)),
% 0.22/0.43    inference(superposition,[],[f246,f227])).
% 0.22/0.43  fof(f246,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl4_33),
% 0.22/0.43    inference(avatar_component_clause,[],[f245])).
% 0.22/0.43  fof(f290,plain,(
% 0.22/0.43    ~spl4_38 | spl4_13 | ~spl4_30),
% 0.22/0.43    inference(avatar_split_clause,[],[f222,f216,f114,f287])).
% 0.22/0.43  fof(f114,plain,(
% 0.22/0.43    spl4_13 <=> v1_xboole_0(sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.43  fof(f216,plain,(
% 0.22/0.43    spl4_30 <=> k1_xboole_0 = sK1),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.43  fof(f222,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | (spl4_13 | ~spl4_30)),
% 0.22/0.43    inference(superposition,[],[f116,f218])).
% 0.22/0.43  fof(f218,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | ~spl4_30),
% 0.22/0.43    inference(avatar_component_clause,[],[f216])).
% 0.22/0.43  fof(f116,plain,(
% 0.22/0.43    ~v1_xboole_0(sK1) | spl4_13),
% 0.22/0.43    inference(avatar_component_clause,[],[f114])).
% 0.22/0.43  fof(f247,plain,(
% 0.22/0.43    spl4_33 | ~spl4_7 | ~spl4_14),
% 0.22/0.43    inference(avatar_split_clause,[],[f147,f119,f87,f245])).
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    spl4_7 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.43  fof(f119,plain,(
% 0.22/0.43    spl4_14 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.43  fof(f147,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) ) | (~spl4_7 | ~spl4_14)),
% 0.22/0.43    inference(resolution,[],[f120,f88])).
% 0.22/0.43  fof(f88,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) ) | ~spl4_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f87])).
% 0.22/0.43  fof(f120,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl4_14),
% 0.22/0.43    inference(avatar_component_clause,[],[f119])).
% 0.22/0.43  fof(f228,plain,(
% 0.22/0.43    spl4_31 | ~spl4_3 | ~spl4_15),
% 0.22/0.43    inference(avatar_split_clause,[],[f148,f123,f71,f226])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    spl4_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.43  fof(f123,plain,(
% 0.22/0.43    spl4_15 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.43  fof(f148,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl4_3 | ~spl4_15)),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f72,f124])).
% 0.22/0.43  fof(f124,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl4_15),
% 0.22/0.43    inference(avatar_component_clause,[],[f123])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f71])).
% 0.22/0.43  fof(f219,plain,(
% 0.22/0.43    spl4_30 | spl4_2 | ~spl4_22 | ~spl4_29),
% 0.22/0.43    inference(avatar_split_clause,[],[f214,f210,f166,f66,f216])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    spl4_2 <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.43  fof(f166,plain,(
% 0.22/0.43    spl4_22 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.43  fof(f210,plain,(
% 0.22/0.43    spl4_29 <=> m1_subset_1(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.43  fof(f214,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | (spl4_2 | ~spl4_22 | ~spl4_29)),
% 0.22/0.43    inference(subsumption_resolution,[],[f178,f212])).
% 0.22/0.43  fof(f212,plain,(
% 0.22/0.43    m1_subset_1(sK0,sK1) | ~spl4_29),
% 0.22/0.43    inference(avatar_component_clause,[],[f210])).
% 0.22/0.43  fof(f178,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | ~m1_subset_1(sK0,sK1) | (spl4_2 | ~spl4_22)),
% 0.22/0.43    inference(resolution,[],[f167,f68])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) | spl4_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f66])).
% 0.22/0.43  fof(f167,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) ) | ~spl4_22),
% 0.22/0.43    inference(avatar_component_clause,[],[f166])).
% 0.22/0.43  fof(f213,plain,(
% 0.22/0.43    spl4_29 | ~spl4_1 | ~spl4_12 | spl4_13),
% 0.22/0.43    inference(avatar_split_clause,[],[f143,f114,f110,f61,f210])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl4_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.43  fof(f110,plain,(
% 0.22/0.43    spl4_12 <=> ! [X1,X0] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.43  fof(f143,plain,(
% 0.22/0.43    m1_subset_1(sK0,sK1) | (~spl4_1 | ~spl4_12 | spl4_13)),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f116,f63,f111])).
% 0.22/0.43  fof(f111,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl4_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f110])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    r2_hidden(sK0,sK1) | ~spl4_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f61])).
% 0.22/0.43  fof(f168,plain,(
% 0.22/0.43    spl4_22),
% 0.22/0.43    inference(avatar_split_clause,[],[f52,f166])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.22/0.43    inference(flattening,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,axiom,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.22/0.43  fof(f140,plain,(
% 0.22/0.43    spl4_18),
% 0.22/0.43    inference(avatar_split_clause,[],[f44,f138])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.43  fof(f133,plain,(
% 0.22/0.43    spl4_17),
% 0.22/0.43    inference(avatar_split_clause,[],[f54,f131])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(nnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.43  fof(f125,plain,(
% 0.22/0.43    spl4_15),
% 0.22/0.43    inference(avatar_split_clause,[],[f51,f123])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.43  fof(f121,plain,(
% 0.22/0.43    spl4_14),
% 0.22/0.43    inference(avatar_split_clause,[],[f50,f119])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f33])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(rectify,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    ~spl4_13 | ~spl4_1 | ~spl4_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f90,f79,f61,f114])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    spl4_5 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    ~v1_xboole_0(sK1) | (~spl4_1 | ~spl4_5)),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f63,f80])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl4_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f79])).
% 0.22/0.43  fof(f112,plain,(
% 0.22/0.43    spl4_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f46,f110])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.43    inference(nnf_transformation,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,axiom,(
% 0.22/0.43    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    spl4_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f42,f87])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(rectify,[],[f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    spl4_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f41,f79])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f31])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl4_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f39,f75])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    spl4_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f38,f71])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    ~spl4_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f37,f66])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.43    inference(negated_conjecture,[],[f17])).
% 0.22/0.43  fof(f17,conjecture,(
% 0.22/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl4_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f36,f61])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    r2_hidden(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f27])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (23966)------------------------------
% 0.22/0.43  % (23966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (23966)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (23966)Memory used [KB]: 6268
% 0.22/0.43  % (23966)Time elapsed: 0.033 s
% 0.22/0.43  % (23966)------------------------------
% 0.22/0.43  % (23966)------------------------------
% 0.22/0.44  % (23958)Success in time 0.077 s
%------------------------------------------------------------------------------
