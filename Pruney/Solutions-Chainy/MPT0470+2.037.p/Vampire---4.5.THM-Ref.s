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
% DateTime   : Thu Dec  3 12:47:49 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 201 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  311 ( 549 expanded)
%              Number of equality atoms :   76 ( 176 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f89,f103,f110,f118,f128,f139,f148,f170,f177,f199,f219,f231])).

fof(f231,plain,
    ( ~ spl1_1
    | ~ spl1_7
    | spl1_15 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_7
    | spl1_15 ),
    inference(subsumption_resolution,[],[f229,f57])).

fof(f57,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f229,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_7
    | spl1_15 ),
    inference(subsumption_resolution,[],[f226,f98])).

fof(f98,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl1_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f226,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_15 ),
    inference(resolution,[],[f218,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f218,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_15 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl1_15
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f219,plain,
    ( ~ spl1_15
    | spl1_6
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f212,f196,f86,f216])).

fof(f86,plain,
    ( spl1_6
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f196,plain,
    ( spl1_14
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f212,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_6
    | ~ spl1_14 ),
    inference(subsumption_resolution,[],[f211,f88])).

fof(f88,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f211,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f210,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f210,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_14 ),
    inference(subsumption_resolution,[],[f209,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f209,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))
    | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f204,f52])).

fof(f204,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0))
    | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_14 ),
    inference(superposition,[],[f80,f198])).

fof(f198,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f196])).

fof(f80,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2)
      | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f199,plain,
    ( spl1_14
    | ~ spl1_1
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f165,f133,f55,f196])).

fof(f133,plain,
    ( spl1_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f165,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_11 ),
    inference(resolution,[],[f134,f57])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f177,plain,
    ( ~ spl1_1
    | ~ spl1_7
    | spl1_13 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_7
    | spl1_13 ),
    inference(subsumption_resolution,[],[f175,f98])).

fof(f175,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_1
    | spl1_13 ),
    inference(subsumption_resolution,[],[f172,f57])).

fof(f172,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_13 ),
    inference(resolution,[],[f169,f43])).

fof(f169,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl1_13
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f170,plain,
    ( ~ spl1_13
    | spl1_5
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f160,f145,f82,f167])).

fof(f82,plain,
    ( spl1_5
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f145,plain,
    ( spl1_12
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f160,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_5
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f159,f84])).

fof(f84,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f159,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f158,f53])).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f158,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f157,f36])).

fof(f157,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0))
    | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f153,f53])).

fof(f153,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0))
    | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_12 ),
    inference(superposition,[],[f80,f147])).

fof(f147,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f148,plain,
    ( spl1_12
    | ~ spl1_1
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f143,f123,f55,f145])).

fof(f123,plain,
    ( spl1_10
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f143,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_1
    | ~ spl1_10 ),
    inference(resolution,[],[f124,f57])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f139,plain,
    ( spl1_11
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f121,f116,f133])).

fof(f116,plain,
    ( spl1_9
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f121,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0)) )
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f120,f36])).

fof(f120,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(X1,k1_xboole_0)))
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0)) )
    | ~ spl1_9 ),
    inference(resolution,[],[f117,f46])).

fof(f117,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f128,plain,
    ( spl1_10
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f113,f101,f123])).

fof(f101,plain,
    ( spl1_8
  <=> ! [X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f113,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X1)) )
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f112,f36])).

fof(f112,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X1)) )
    | ~ spl1_8 ),
    inference(resolution,[],[f102,f46])).

fof(f102,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f118,plain,
    ( spl1_9
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f114,f97,f70,f116])).

fof(f70,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f114,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f95,f98])).

fof(f95,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(superposition,[],[f41,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f110,plain,
    ( ~ spl1_2
    | spl1_7 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl1_2
    | spl1_7 ),
    inference(subsumption_resolution,[],[f107,f62])).

fof(f62,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f107,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_7 ),
    inference(resolution,[],[f99,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f99,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f103,plain,
    ( ~ spl1_7
    | spl1_8
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f91,f65,f101,f97])).

fof(f65,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f91,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3 ),
    inference(superposition,[],[f40,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f89,plain,
    ( ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f32,f86,f82])).

fof(f32,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f73,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f68,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.41/0.54  % (17066)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.41/0.54  % (17069)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.41/0.55  % (17066)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f232,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f89,f103,f110,f118,f128,f139,f148,f170,f177,f199,f219,f231])).
% 1.41/0.55  fof(f231,plain,(
% 1.41/0.55    ~spl1_1 | ~spl1_7 | spl1_15),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f230])).
% 1.41/0.55  fof(f230,plain,(
% 1.41/0.55    $false | (~spl1_1 | ~spl1_7 | spl1_15)),
% 1.41/0.55    inference(subsumption_resolution,[],[f229,f57])).
% 1.41/0.55  fof(f57,plain,(
% 1.41/0.55    v1_relat_1(sK0) | ~spl1_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f55])).
% 1.41/0.55  fof(f55,plain,(
% 1.41/0.55    spl1_1 <=> v1_relat_1(sK0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.41/0.55  fof(f229,plain,(
% 1.41/0.55    ~v1_relat_1(sK0) | (~spl1_7 | spl1_15)),
% 1.41/0.55    inference(subsumption_resolution,[],[f226,f98])).
% 1.41/0.55  fof(f98,plain,(
% 1.41/0.55    v1_relat_1(k1_xboole_0) | ~spl1_7),
% 1.41/0.55    inference(avatar_component_clause,[],[f97])).
% 1.41/0.55  fof(f97,plain,(
% 1.41/0.55    spl1_7 <=> v1_relat_1(k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 1.41/0.55  fof(f226,plain,(
% 1.41/0.55    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_15),
% 1.41/0.55    inference(resolution,[],[f218,f43])).
% 1.41/0.55  fof(f43,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f24])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(flattening,[],[f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.41/0.55  fof(f218,plain,(
% 1.41/0.55    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_15),
% 1.41/0.55    inference(avatar_component_clause,[],[f216])).
% 1.41/0.55  fof(f216,plain,(
% 1.41/0.55    spl1_15 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 1.41/0.55  fof(f219,plain,(
% 1.41/0.55    ~spl1_15 | spl1_6 | ~spl1_14),
% 1.41/0.55    inference(avatar_split_clause,[],[f212,f196,f86,f216])).
% 1.41/0.55  fof(f86,plain,(
% 1.41/0.55    spl1_6 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.41/0.55  fof(f196,plain,(
% 1.41/0.55    spl1_14 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 1.41/0.55  fof(f212,plain,(
% 1.41/0.55    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (spl1_6 | ~spl1_14)),
% 1.41/0.55    inference(subsumption_resolution,[],[f211,f88])).
% 1.41/0.55  fof(f88,plain,(
% 1.41/0.55    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_6),
% 1.41/0.55    inference(avatar_component_clause,[],[f86])).
% 1.41/0.55  fof(f211,plain,(
% 1.41/0.55    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_14),
% 1.41/0.55    inference(forward_demodulation,[],[f210,f52])).
% 1.41/0.55  fof(f52,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f49])).
% 1.41/0.55  fof(f49,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.41/0.55    inference(cnf_transformation,[],[f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.55    inference(flattening,[],[f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.55    inference(nnf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.41/0.55  fof(f210,plain,(
% 1.41/0.55    k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f209,f36])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.41/0.55  fof(f209,plain,(
% 1.41/0.55    ~r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_14),
% 1.41/0.55    inference(forward_demodulation,[],[f204,f52])).
% 1.41/0.55  fof(f204,plain,(
% 1.41/0.55    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) | k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_14),
% 1.41/0.55    inference(superposition,[],[f80,f198])).
% 1.41/0.55  fof(f198,plain,(
% 1.41/0.55    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_14),
% 1.41/0.55    inference(avatar_component_clause,[],[f196])).
% 1.41/0.55  fof(f80,plain,(
% 1.41/0.55    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2) | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2 | ~v1_relat_1(X2)) )),
% 1.41/0.55    inference(resolution,[],[f46,f39])).
% 1.41/0.55  fof(f39,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.41/0.55  fof(f46,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.55    inference(flattening,[],[f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.55    inference(nnf_transformation,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.55  fof(f199,plain,(
% 1.41/0.55    spl1_14 | ~spl1_1 | ~spl1_11),
% 1.41/0.55    inference(avatar_split_clause,[],[f165,f133,f55,f196])).
% 1.41/0.55  fof(f133,plain,(
% 1.41/0.55    spl1_11 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 1.41/0.55  fof(f165,plain,(
% 1.41/0.55    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_1 | ~spl1_11)),
% 1.41/0.55    inference(resolution,[],[f134,f57])).
% 1.41/0.55  fof(f134,plain,(
% 1.41/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | ~spl1_11),
% 1.41/0.55    inference(avatar_component_clause,[],[f133])).
% 1.41/0.55  fof(f177,plain,(
% 1.41/0.55    ~spl1_1 | ~spl1_7 | spl1_13),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f176])).
% 1.41/0.55  fof(f176,plain,(
% 1.41/0.55    $false | (~spl1_1 | ~spl1_7 | spl1_13)),
% 1.41/0.55    inference(subsumption_resolution,[],[f175,f98])).
% 1.41/0.55  fof(f175,plain,(
% 1.41/0.55    ~v1_relat_1(k1_xboole_0) | (~spl1_1 | spl1_13)),
% 1.41/0.55    inference(subsumption_resolution,[],[f172,f57])).
% 1.41/0.55  fof(f172,plain,(
% 1.41/0.55    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_13),
% 1.41/0.55    inference(resolution,[],[f169,f43])).
% 1.41/0.55  fof(f169,plain,(
% 1.41/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_13),
% 1.41/0.55    inference(avatar_component_clause,[],[f167])).
% 1.41/0.55  fof(f167,plain,(
% 1.41/0.55    spl1_13 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 1.41/0.55  fof(f170,plain,(
% 1.41/0.55    ~spl1_13 | spl1_5 | ~spl1_12),
% 1.41/0.55    inference(avatar_split_clause,[],[f160,f145,f82,f167])).
% 1.41/0.55  fof(f82,plain,(
% 1.41/0.55    spl1_5 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.41/0.55  fof(f145,plain,(
% 1.41/0.55    spl1_12 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 1.41/0.55  fof(f160,plain,(
% 1.41/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (spl1_5 | ~spl1_12)),
% 1.41/0.55    inference(subsumption_resolution,[],[f159,f84])).
% 1.41/0.55  fof(f84,plain,(
% 1.41/0.55    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_5),
% 1.41/0.55    inference(avatar_component_clause,[],[f82])).
% 1.41/0.55  fof(f159,plain,(
% 1.41/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_12),
% 1.41/0.55    inference(forward_demodulation,[],[f158,f53])).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.41/0.55    inference(equality_resolution,[],[f48])).
% 1.41/0.55  fof(f48,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f30])).
% 1.41/0.55  fof(f158,plain,(
% 1.41/0.55    k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_12),
% 1.41/0.55    inference(subsumption_resolution,[],[f157,f36])).
% 1.41/0.55  fof(f157,plain,(
% 1.41/0.55    ~r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_12),
% 1.41/0.55    inference(forward_demodulation,[],[f153,f53])).
% 1.41/0.55  fof(f153,plain,(
% 1.41/0.55    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_12),
% 1.41/0.55    inference(superposition,[],[f80,f147])).
% 1.41/0.55  fof(f147,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_12),
% 1.41/0.55    inference(avatar_component_clause,[],[f145])).
% 1.41/0.55  fof(f148,plain,(
% 1.41/0.55    spl1_12 | ~spl1_1 | ~spl1_10),
% 1.41/0.55    inference(avatar_split_clause,[],[f143,f123,f55,f145])).
% 1.41/0.55  fof(f123,plain,(
% 1.41/0.55    spl1_10 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 1.41/0.55  fof(f143,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_1 | ~spl1_10)),
% 1.41/0.55    inference(resolution,[],[f124,f57])).
% 1.41/0.55  fof(f124,plain,(
% 1.41/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_10),
% 1.41/0.55    inference(avatar_component_clause,[],[f123])).
% 1.41/0.55  fof(f139,plain,(
% 1.41/0.55    spl1_11 | ~spl1_9),
% 1.41/0.55    inference(avatar_split_clause,[],[f121,f116,f133])).
% 1.41/0.55  fof(f116,plain,(
% 1.41/0.55    spl1_9 <=> ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 1.41/0.55  fof(f121,plain,(
% 1.41/0.55    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0))) ) | ~spl1_9),
% 1.41/0.55    inference(subsumption_resolution,[],[f120,f36])).
% 1.41/0.55  fof(f120,plain,(
% 1.41/0.55    ( ! [X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(X1,k1_xboole_0))) | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0))) ) | ~spl1_9),
% 1.41/0.55    inference(resolution,[],[f117,f46])).
% 1.41/0.55  fof(f117,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_9),
% 1.41/0.55    inference(avatar_component_clause,[],[f116])).
% 1.41/0.55  fof(f128,plain,(
% 1.41/0.55    spl1_10 | ~spl1_8),
% 1.41/0.55    inference(avatar_split_clause,[],[f113,f101,f123])).
% 1.41/0.55  fof(f101,plain,(
% 1.41/0.55    spl1_8 <=> ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 1.41/0.55  fof(f113,plain,(
% 1.41/0.55    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X1))) ) | ~spl1_8),
% 1.41/0.55    inference(subsumption_resolution,[],[f112,f36])).
% 1.41/0.55  fof(f112,plain,(
% 1.41/0.55    ( ! [X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X1))) ) | ~spl1_8),
% 1.41/0.55    inference(resolution,[],[f102,f46])).
% 1.41/0.55  fof(f102,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_8),
% 1.41/0.55    inference(avatar_component_clause,[],[f101])).
% 1.41/0.55  fof(f118,plain,(
% 1.41/0.55    spl1_9 | ~spl1_4 | ~spl1_7),
% 1.41/0.55    inference(avatar_split_clause,[],[f114,f97,f70,f116])).
% 1.41/0.55  fof(f70,plain,(
% 1.41/0.55    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.41/0.55  fof(f114,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | (~spl1_4 | ~spl1_7)),
% 1.41/0.55    inference(subsumption_resolution,[],[f95,f98])).
% 1.41/0.55  fof(f95,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 1.41/0.55    inference(superposition,[],[f41,f72])).
% 1.41/0.55  fof(f72,plain,(
% 1.41/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 1.41/0.55    inference(avatar_component_clause,[],[f70])).
% 1.41/0.55  fof(f41,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f20])).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.41/0.55  fof(f110,plain,(
% 1.41/0.55    ~spl1_2 | spl1_7),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f109])).
% 1.41/0.55  fof(f109,plain,(
% 1.41/0.55    $false | (~spl1_2 | spl1_7)),
% 1.41/0.55    inference(subsumption_resolution,[],[f107,f62])).
% 1.41/0.55  fof(f62,plain,(
% 1.41/0.55    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f60])).
% 1.41/0.55  fof(f60,plain,(
% 1.41/0.55    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.41/0.55  fof(f107,plain,(
% 1.41/0.55    ~v1_xboole_0(k1_xboole_0) | spl1_7),
% 1.41/0.55    inference(resolution,[],[f99,f37])).
% 1.41/0.55  fof(f37,plain,(
% 1.41/0.55    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f16])).
% 1.41/0.55  fof(f16,plain,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f6])).
% 1.41/0.55  fof(f6,axiom,(
% 1.41/0.55    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.41/0.55  fof(f99,plain,(
% 1.41/0.55    ~v1_relat_1(k1_xboole_0) | spl1_7),
% 1.41/0.55    inference(avatar_component_clause,[],[f97])).
% 1.41/0.55  fof(f103,plain,(
% 1.41/0.55    ~spl1_7 | spl1_8 | ~spl1_3),
% 1.41/0.55    inference(avatar_split_clause,[],[f91,f65,f101,f97])).
% 1.41/0.55  fof(f65,plain,(
% 1.41/0.55    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.41/0.55  fof(f91,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_3),
% 1.41/0.55    inference(superposition,[],[f40,f67])).
% 1.41/0.55  fof(f67,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 1.41/0.55    inference(avatar_component_clause,[],[f65])).
% 1.41/0.55  fof(f40,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f19])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.41/0.55  fof(f89,plain,(
% 1.41/0.55    ~spl1_5 | ~spl1_6),
% 1.41/0.55    inference(avatar_split_clause,[],[f32,f86,f82])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f26])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f15,plain,(
% 1.41/0.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f14])).
% 1.41/0.55  fof(f14,negated_conjecture,(
% 1.41/0.55    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.41/0.55    inference(negated_conjecture,[],[f13])).
% 1.41/0.55  fof(f13,conjecture,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.41/0.55  fof(f73,plain,(
% 1.41/0.55    spl1_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f35,f70])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.41/0.55    inference(cnf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,axiom,(
% 1.41/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.41/0.55  fof(f68,plain,(
% 1.41/0.55    spl1_3),
% 1.41/0.55    inference(avatar_split_clause,[],[f34,f65])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.55    inference(cnf_transformation,[],[f12])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    spl1_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f33,f60])).
% 1.41/0.55  fof(f33,plain,(
% 1.41/0.55    v1_xboole_0(k1_xboole_0)),
% 1.41/0.55    inference(cnf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    v1_xboole_0(k1_xboole_0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.41/0.55  fof(f58,plain,(
% 1.41/0.55    spl1_1),
% 1.41/0.55    inference(avatar_split_clause,[],[f31,f55])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    v1_relat_1(sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f26])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (17066)------------------------------
% 1.41/0.55  % (17066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (17066)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (17066)Memory used [KB]: 6268
% 1.41/0.55  % (17066)Time elapsed: 0.137 s
% 1.41/0.55  % (17066)------------------------------
% 1.41/0.55  % (17066)------------------------------
% 1.41/0.55  % (17070)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.41/0.55  % (17064)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.41/0.55  % (17068)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.55/0.56  % (17067)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.55/0.56  % (17063)Success in time 0.204 s
%------------------------------------------------------------------------------
