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
% DateTime   : Thu Dec  3 12:42:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 164 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :    6
%              Number of atoms          :  289 ( 483 expanded)
%              Number of equality atoms :   32 (  52 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f43,f48,f52,f56,f60,f64,f68,f72,f76,f80,f85,f183,f251,f261,f263,f277,f299,f318])).

fof(f318,plain,
    ( spl4_23
    | ~ spl4_5
    | ~ spl4_10
    | spl4_22
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f317,f180,f143,f70,f50,f147])).

fof(f147,plain,
    ( spl4_23
  <=> ! [X0] : r1_tarski(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f50,plain,
    ( spl4_5
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f70,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f143,plain,
    ( spl4_22
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f180,plain,
    ( spl4_30
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f317,plain,
    ( ! [X2] : r1_tarski(sK0,X2)
    | ~ spl4_5
    | ~ spl4_10
    | spl4_22
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f316,f144])).

fof(f144,plain,
    ( k1_xboole_0 != sK1
    | spl4_22 ),
    inference(avatar_component_clause,[],[f143])).

fof(f316,plain,
    ( ! [X2] :
        ( r1_tarski(sK0,X2)
        | k1_xboole_0 = sK1 )
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f302,f51])).

fof(f51,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f302,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X2,sK1))
        | r1_tarski(sK0,X2)
        | k1_xboole_0 = sK1 )
    | ~ spl4_10
    | ~ spl4_30 ),
    inference(superposition,[],[f71,f182])).

fof(f182,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f180])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
        | r1_tarski(X1,X2)
        | k1_xboole_0 = X0 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f299,plain,
    ( ~ spl4_13
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl4_13
    | ~ spl4_40 ),
    inference(resolution,[],[f260,f84])).

fof(f84,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_13
  <=> ! [X1,X0] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f260,plain,
    ( ! [X0] : ~ r1_xboole_0(sK0,X0)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl4_40
  <=> ! [X0] : ~ r1_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f277,plain,
    ( spl4_1
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl4_1
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f270,f51])).

fof(f270,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl4_1
    | ~ spl4_22 ),
    inference(superposition,[],[f33,f145])).

fof(f145,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f143])).

fof(f33,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f263,plain,
    ( spl4_22
    | spl4_23
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f141,f112,f66,f50,f147,f143])).

fof(f66,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f112,plain,
    ( spl4_19
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f141,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,X0)
        | k1_xboole_0 = sK1 )
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f128,f51])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,X0))
        | r1_tarski(sK0,X0)
        | k1_xboole_0 = sK1 )
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(superposition,[],[f67,f114])).

fof(f114,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f112])).

fof(f67,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(X1,X2)
        | k1_xboole_0 = X0 )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f261,plain,
    ( spl4_40
    | spl4_4
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f257,f147,f58,f45,f259])).

fof(f45,plain,
    ( spl4_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f58,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(X1,X0)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f257,plain,
    ( ! [X0] : ~ r1_xboole_0(sK0,X0)
    | spl4_4
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f256,f47])).

fof(f47,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK0,X0)
        | v1_xboole_0(sK0) )
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(resolution,[],[f148,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | ~ r1_xboole_0(X1,X0)
        | v1_xboole_0(X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f148,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f251,plain,
    ( spl4_19
    | spl4_1
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f124,f78,f40,f31,f112])).

fof(f40,plain,
    ( spl4_3
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f78,plain,
    ( spl4_12
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(X0,X2)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f124,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f123,f33])).

fof(f123,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | r1_tarski(sK1,sK3)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(resolution,[],[f79,f42])).

fof(f42,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f79,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | r1_tarski(X0,X2) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f183,plain,
    ( spl4_30
    | spl4_1
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f178,f74,f36,f31,f180])).

fof(f36,plain,
    ( spl4_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f74,plain,
    ( spl4_11
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(X1,X3)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f178,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f176,f33])).

fof(f176,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK1,sK3)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(resolution,[],[f38,f75])).

fof(f75,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | r1_tarski(X1,X3) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f38,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f85,plain,
    ( spl4_13
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f81,f62,f54,f83])).

fof(f54,plain,
    ( spl4_6
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f62,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f81,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f63,f55])).

fof(f55,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f80,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f28,f78])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f76,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f29,f74])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f68,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f25,f62])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f60,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f56,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f52,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(sK1,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3,X2,X1] :
        ( ~ r1_tarski(X1,X3)
        & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
          | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
   => ( ~ r1_tarski(sK1,sK3)
      & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
        | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f43,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f20,f40,f36])).

fof(f20,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (7538)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (7538)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f332,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f34,f43,f48,f52,f56,f60,f64,f68,f72,f76,f80,f85,f183,f251,f261,f263,f277,f299,f318])).
% 0.20/0.42  fof(f318,plain,(
% 0.20/0.42    spl4_23 | ~spl4_5 | ~spl4_10 | spl4_22 | ~spl4_30),
% 0.20/0.42    inference(avatar_split_clause,[],[f317,f180,f143,f70,f50,f147])).
% 0.20/0.42  fof(f147,plain,(
% 0.20/0.42    spl4_23 <=> ! [X0] : r1_tarski(sK0,X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl4_5 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    spl4_10 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.42  fof(f143,plain,(
% 0.20/0.42    spl4_22 <=> k1_xboole_0 = sK1),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.42  fof(f180,plain,(
% 0.20/0.42    spl4_30 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.42  fof(f317,plain,(
% 0.20/0.42    ( ! [X2] : (r1_tarski(sK0,X2)) ) | (~spl4_5 | ~spl4_10 | spl4_22 | ~spl4_30)),
% 0.20/0.42    inference(subsumption_resolution,[],[f316,f144])).
% 0.20/0.42  fof(f144,plain,(
% 0.20/0.42    k1_xboole_0 != sK1 | spl4_22),
% 0.20/0.42    inference(avatar_component_clause,[],[f143])).
% 0.20/0.42  fof(f316,plain,(
% 0.20/0.42    ( ! [X2] : (r1_tarski(sK0,X2) | k1_xboole_0 = sK1) ) | (~spl4_5 | ~spl4_10 | ~spl4_30)),
% 0.20/0.42    inference(subsumption_resolution,[],[f302,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f50])).
% 0.20/0.42  fof(f302,plain,(
% 0.20/0.42    ( ! [X2] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X2,sK1)) | r1_tarski(sK0,X2) | k1_xboole_0 = sK1) ) | (~spl4_10 | ~spl4_30)),
% 0.20/0.42    inference(superposition,[],[f71,f182])).
% 0.20/0.42  fof(f182,plain,(
% 0.20/0.42    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_30),
% 0.20/0.42    inference(avatar_component_clause,[],[f180])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) ) | ~spl4_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f70])).
% 0.20/0.42  fof(f299,plain,(
% 0.20/0.42    ~spl4_13 | ~spl4_40),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f298])).
% 0.20/0.42  fof(f298,plain,(
% 0.20/0.42    $false | (~spl4_13 | ~spl4_40)),
% 0.20/0.42    inference(resolution,[],[f260,f84])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl4_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f83])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    spl4_13 <=> ! [X1,X0] : r1_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.42  fof(f260,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_xboole_0(sK0,X0)) ) | ~spl4_40),
% 0.20/0.42    inference(avatar_component_clause,[],[f259])).
% 0.20/0.42  fof(f259,plain,(
% 0.20/0.42    spl4_40 <=> ! [X0] : ~r1_xboole_0(sK0,X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.20/0.42  fof(f277,plain,(
% 0.20/0.42    spl4_1 | ~spl4_5 | ~spl4_22),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f276])).
% 0.20/0.42  fof(f276,plain,(
% 0.20/0.42    $false | (spl4_1 | ~spl4_5 | ~spl4_22)),
% 0.20/0.42    inference(subsumption_resolution,[],[f270,f51])).
% 0.20/0.42  fof(f270,plain,(
% 0.20/0.42    ~r1_tarski(k1_xboole_0,sK3) | (spl4_1 | ~spl4_22)),
% 0.20/0.42    inference(superposition,[],[f33,f145])).
% 0.20/0.42  fof(f145,plain,(
% 0.20/0.42    k1_xboole_0 = sK1 | ~spl4_22),
% 0.20/0.42    inference(avatar_component_clause,[],[f143])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ~r1_tarski(sK1,sK3) | spl4_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    spl4_1 <=> r1_tarski(sK1,sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.42  fof(f263,plain,(
% 0.20/0.42    spl4_22 | spl4_23 | ~spl4_5 | ~spl4_9 | ~spl4_19),
% 0.20/0.42    inference(avatar_split_clause,[],[f141,f112,f66,f50,f147,f143])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl4_9 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.42  fof(f112,plain,(
% 0.20/0.42    spl4_19 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.42  fof(f141,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(sK0,X0) | k1_xboole_0 = sK1) ) | (~spl4_5 | ~spl4_9 | ~spl4_19)),
% 0.20/0.42    inference(subsumption_resolution,[],[f128,f51])).
% 0.20/0.42  fof(f128,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,X0)) | r1_tarski(sK0,X0) | k1_xboole_0 = sK1) ) | (~spl4_9 | ~spl4_19)),
% 0.20/0.42    inference(superposition,[],[f67,f114])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl4_19),
% 0.20/0.42    inference(avatar_component_clause,[],[f112])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) ) | ~spl4_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f66])).
% 0.20/0.42  fof(f261,plain,(
% 0.20/0.42    spl4_40 | spl4_4 | ~spl4_7 | ~spl4_23),
% 0.20/0.42    inference(avatar_split_clause,[],[f257,f147,f58,f45,f259])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl4_4 <=> v1_xboole_0(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl4_7 <=> ! [X1,X0] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.42  fof(f257,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_xboole_0(sK0,X0)) ) | (spl4_4 | ~spl4_7 | ~spl4_23)),
% 0.20/0.42    inference(subsumption_resolution,[],[f256,f47])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ~v1_xboole_0(sK0) | spl4_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f45])).
% 0.20/0.42  fof(f256,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_xboole_0(sK0,X0) | v1_xboole_0(sK0)) ) | (~spl4_7 | ~spl4_23)),
% 0.20/0.42    inference(resolution,[],[f148,f59])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) ) | ~spl4_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f58])).
% 0.20/0.42  fof(f148,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(sK0,X0)) ) | ~spl4_23),
% 0.20/0.42    inference(avatar_component_clause,[],[f147])).
% 0.20/0.42  fof(f251,plain,(
% 0.20/0.42    spl4_19 | spl4_1 | ~spl4_3 | ~spl4_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f124,f78,f40,f31,f112])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl4_3 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl4_12 <=> ! [X1,X3,X0,X2] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.42  fof(f124,plain,(
% 0.20/0.42    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | (spl4_1 | ~spl4_3 | ~spl4_12)),
% 0.20/0.42    inference(subsumption_resolution,[],[f123,f33])).
% 0.20/0.42  fof(f123,plain,(
% 0.20/0.42    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | r1_tarski(sK1,sK3) | (~spl4_3 | ~spl4_12)),
% 0.20/0.42    inference(resolution,[],[f79,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | ~spl4_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f40])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X0,X2)) ) | ~spl4_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f78])).
% 0.20/0.42  fof(f183,plain,(
% 0.20/0.42    spl4_30 | spl4_1 | ~spl4_2 | ~spl4_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f178,f74,f36,f31,f180])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    spl4_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    spl4_11 <=> ! [X1,X3,X0,X2] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.42  fof(f178,plain,(
% 0.20/0.42    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl4_1 | ~spl4_2 | ~spl4_11)),
% 0.20/0.42    inference(subsumption_resolution,[],[f176,f33])).
% 0.20/0.42  fof(f176,plain,(
% 0.20/0.42    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK1,sK3) | (~spl4_2 | ~spl4_11)),
% 0.20/0.42    inference(resolution,[],[f38,f75])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X1,X3)) ) | ~spl4_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f74])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f36])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    spl4_13 | ~spl4_6 | ~spl4_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f81,f62,f54,f83])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    spl4_6 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    spl4_8 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) ) | (~spl4_6 | ~spl4_8)),
% 0.20/0.42    inference(resolution,[],[f63,f55])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl4_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f54])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f62])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    spl4_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f78])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.42    inference(flattening,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl4_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f29,f74])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    spl4_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f70])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl4_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f66])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    spl4_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f62])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    spl4_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f58])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl4_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f54])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    spl4_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f50])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ~spl4_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f45])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ~v1_xboole_0(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) & ~v1_xboole_0(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17,f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0)) => (? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) => (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl4_2 | spl4_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f40,f36])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ~spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f31])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ~r1_tarski(sK1,sK3)),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (7538)------------------------------
% 0.20/0.43  % (7538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (7538)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (7538)Memory used [KB]: 10746
% 0.20/0.43  % (7538)Time elapsed: 0.009 s
% 0.20/0.43  % (7538)------------------------------
% 0.20/0.43  % (7538)------------------------------
% 0.20/0.43  % (7532)Success in time 0.068 s
%------------------------------------------------------------------------------
