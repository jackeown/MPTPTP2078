%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 203 expanded)
%              Number of leaves         :   28 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  354 ( 535 expanded)
%              Number of equality atoms :   81 ( 133 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f81,f95,f116,f121,f125,f137,f141,f155,f266,f300,f318])).

fof(f318,plain,
    ( ~ spl1_1
    | spl1_6
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl1_1
    | spl1_6
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f316,f90])).

fof(f90,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl1_6
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f316,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_1
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f315,f124])).

fof(f124,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl1_10
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f315,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_1
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f314,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f314,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0))
    | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_1
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f313,f124])).

fof(f313,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0))
    | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_1
    | ~ spl1_8
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f312,f111])).

fof(f111,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl1_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f312,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0))
    | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f306,f53])).

fof(f53,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f306,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0))
    | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_13 ),
    inference(superposition,[],[f211,f154])).

fof(f154,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl1_13
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f211,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2))),k5_relat_1(X1,X2))
      | k5_relat_1(X1,X2) = k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

% (27914)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f84,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2) ) ),
    inference(resolution,[],[f47,f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f300,plain,
    ( spl1_7
    | ~ spl1_5
    | ~ spl1_11
    | ~ spl1_21 ),
    inference(avatar_split_clause,[],[f279,f248,f134,f79,f92])).

fof(f92,plain,
    ( spl1_7
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f79,plain,
    ( spl1_5
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f134,plain,
    ( spl1_11
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f248,plain,
    ( spl1_21
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f279,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_11
    | ~ spl1_21 ),
    inference(subsumption_resolution,[],[f278,f36])).

fof(f278,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_11
    | ~ spl1_21 ),
    inference(forward_demodulation,[],[f277,f80])).

fof(f80,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f277,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_11
    | ~ spl1_21 ),
    inference(forward_demodulation,[],[f276,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f276,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_5
    | ~ spl1_11
    | ~ spl1_21 ),
    inference(forward_demodulation,[],[f275,f80])).

fof(f275,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_11
    | ~ spl1_21 ),
    inference(forward_demodulation,[],[f272,f136])).

fof(f272,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_21 ),
    inference(resolution,[],[f249,f84])).

fof(f249,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f248])).

fof(f266,plain,
    ( ~ spl1_1
    | ~ spl1_8
    | spl1_21 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_8
    | spl1_21 ),
    inference(subsumption_resolution,[],[f264,f53])).

fof(f264,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_8
    | spl1_21 ),
    inference(subsumption_resolution,[],[f261,f111])).

fof(f261,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_21 ),
    inference(resolution,[],[f250,f44])).

fof(f250,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_21 ),
    inference(avatar_component_clause,[],[f248])).

fof(f155,plain,
    ( spl1_13
    | ~ spl1_1
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f150,f139,f51,f152])).

fof(f139,plain,
    ( spl1_12
  <=> ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f150,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_1
    | ~ spl1_12 ),
    inference(resolution,[],[f140,f53])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( spl1_12
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f132,f110,f66,f61,f139])).

fof(f61,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f66,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f132,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f105,f111])).

% (27909)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f105,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f104,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f104,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4 ),
    inference(superposition,[],[f41,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f137,plain,
    ( spl1_11
    | ~ spl1_1
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f129,f114,f51,f134])).

fof(f114,plain,
    ( spl1_9
  <=> ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f129,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_9 ),
    inference(resolution,[],[f115,f53])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f125,plain,
    ( spl1_10
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f106,f56,f123])).

fof(f56,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f106,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl1_2 ),
    inference(resolution,[],[f72,f58])).

fof(f58,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f121,plain,
    ( ~ spl1_2
    | spl1_8 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl1_2
    | spl1_8 ),
    inference(subsumption_resolution,[],[f118,f58])).

fof(f118,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_8 ),
    inference(resolution,[],[f112,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f112,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f116,plain,
    ( ~ spl1_8
    | spl1_9
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f99,f66,f61,f114,f110])).

fof(f99,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f98,f68])).

fof(f98,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f96,f36])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3 ),
    inference(superposition,[],[f40,f63])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f95,plain,
    ( ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f32,f92,f88])).

fof(f32,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).

fof(f27,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f81,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f73,f56,f79])).

fof(f73,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl1_2 ),
    inference(resolution,[],[f71,f58])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f42,f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f69,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f64,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f33,f56])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f54,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f31,f51])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:56:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (27905)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (27904)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (27911)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (27907)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (27906)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (27926)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (27903)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (27919)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (27921)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (27904)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (27924)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (27927)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (27908)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (27903)Refutation not found, incomplete strategy% (27903)------------------------------
% 0.20/0.52  % (27903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27903)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27903)Memory used [KB]: 10490
% 0.20/0.52  % (27903)Time elapsed: 0.096 s
% 0.20/0.52  % (27903)------------------------------
% 0.20/0.52  % (27903)------------------------------
% 0.20/0.52  % (27908)Refutation not found, incomplete strategy% (27908)------------------------------
% 0.20/0.52  % (27908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27908)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27908)Memory used [KB]: 10618
% 0.20/0.52  % (27908)Time elapsed: 0.093 s
% 0.20/0.52  % (27908)------------------------------
% 0.20/0.52  % (27908)------------------------------
% 0.20/0.52  % (27913)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (27916)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (27922)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (27912)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (27918)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (27910)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f327,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f81,f95,f116,f121,f125,f137,f141,f155,f266,f300,f318])).
% 0.20/0.53  fof(f318,plain,(
% 0.20/0.53    ~spl1_1 | spl1_6 | ~spl1_8 | ~spl1_10 | ~spl1_13),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f317])).
% 0.20/0.53  fof(f317,plain,(
% 0.20/0.53    $false | (~spl1_1 | spl1_6 | ~spl1_8 | ~spl1_10 | ~spl1_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f316,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    spl1_6 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.53  fof(f316,plain,(
% 0.20/0.53    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl1_1 | ~spl1_8 | ~spl1_10 | ~spl1_13)),
% 0.20/0.53    inference(forward_demodulation,[],[f315,f124])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | ~spl1_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f123])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    spl1_10 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.53  fof(f315,plain,(
% 0.20/0.53    k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_1 | ~spl1_8 | ~spl1_10 | ~spl1_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f314,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f314,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_1 | ~spl1_8 | ~spl1_10 | ~spl1_13)),
% 0.20/0.53    inference(forward_demodulation,[],[f313,f124])).
% 0.20/0.53  fof(f313,plain,(
% 0.20/0.53    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_1 | ~spl1_8 | ~spl1_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f312,f111])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    v1_relat_1(k1_xboole_0) | ~spl1_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f110])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    spl1_8 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.53  fof(f312,plain,(
% 0.20/0.53    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(k1_xboole_0) | (~spl1_1 | ~spl1_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f306,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    v1_relat_1(sK0) | ~spl1_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    spl1_1 <=> v1_relat_1(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.53  fof(f306,plain,(
% 0.20/0.53    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) | k5_relat_1(k1_xboole_0,sK0) = k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~spl1_13),
% 0.20/0.53    inference(superposition,[],[f211,f154])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f152])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    spl1_13 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2))),k5_relat_1(X1,X2)) | k5_relat_1(X1,X2) = k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2))) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(resolution,[],[f84,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.53  % (27914)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X2] : (~v1_relat_1(X2) | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) = X2 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)),X2)) )),
% 0.20/0.53    inference(resolution,[],[f47,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f300,plain,(
% 0.20/0.53    spl1_7 | ~spl1_5 | ~spl1_11 | ~spl1_21),
% 0.20/0.53    inference(avatar_split_clause,[],[f279,f248,f134,f79,f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    spl1_7 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    spl1_5 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    spl1_11 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    spl1_21 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.20/0.53  fof(f279,plain,(
% 0.20/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_5 | ~spl1_11 | ~spl1_21)),
% 0.20/0.53    inference(subsumption_resolution,[],[f278,f36])).
% 0.20/0.53  fof(f278,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_5 | ~spl1_11 | ~spl1_21)),
% 0.20/0.53    inference(forward_demodulation,[],[f277,f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl1_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f79])).
% 0.20/0.53  fof(f277,plain,(
% 0.20/0.53    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_5 | ~spl1_11 | ~spl1_21)),
% 0.20/0.53    inference(forward_demodulation,[],[f276,f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f134])).
% 0.20/0.53  fof(f276,plain,(
% 0.20/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0)) | (~spl1_5 | ~spl1_11 | ~spl1_21)),
% 0.20/0.53    inference(forward_demodulation,[],[f275,f80])).
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0)) | (~spl1_11 | ~spl1_21)),
% 0.20/0.53    inference(forward_demodulation,[],[f272,f136])).
% 0.20/0.53  fof(f272,plain,(
% 0.20/0.53    k5_relat_1(sK0,k1_xboole_0) = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),k5_relat_1(sK0,k1_xboole_0)) | ~spl1_21),
% 0.20/0.53    inference(resolution,[],[f249,f84])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_21),
% 0.20/0.53    inference(avatar_component_clause,[],[f248])).
% 0.20/0.53  fof(f266,plain,(
% 0.20/0.53    ~spl1_1 | ~spl1_8 | spl1_21),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f265])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    $false | (~spl1_1 | ~spl1_8 | spl1_21)),
% 0.20/0.53    inference(subsumption_resolution,[],[f264,f53])).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    ~v1_relat_1(sK0) | (~spl1_8 | spl1_21)),
% 0.20/0.53    inference(subsumption_resolution,[],[f261,f111])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_21),
% 0.20/0.53    inference(resolution,[],[f250,f44])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_21),
% 0.20/0.53    inference(avatar_component_clause,[],[f248])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    spl1_13 | ~spl1_1 | ~spl1_12),
% 0.20/0.53    inference(avatar_split_clause,[],[f150,f139,f51,f152])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    spl1_12 <=> ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_1 | ~spl1_12)),
% 0.20/0.53    inference(resolution,[],[f140,f53])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f139])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    spl1_12 | ~spl1_3 | ~spl1_4 | ~spl1_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f132,f110,f66,f61,f139])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f105,f111])).
% 0.20/0.53  % (27909)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_4)),
% 0.20/0.53    inference(forward_demodulation,[],[f104,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f61])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f102,f36])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_4),
% 0.20/0.53    inference(superposition,[],[f41,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f66])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    spl1_11 | ~spl1_1 | ~spl1_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f129,f114,f51,f134])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    spl1_9 <=> ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_1 | ~spl1_9)),
% 0.20/0.53    inference(resolution,[],[f115,f53])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | ~spl1_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f114])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    spl1_10 | ~spl1_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f106,f56,f123])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | ~spl1_2),
% 0.20/0.53    inference(resolution,[],[f72,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f56])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f43,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ~spl1_2 | spl1_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f120])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    $false | (~spl1_2 | spl1_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f118,f58])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ~v1_xboole_0(k1_xboole_0) | spl1_8),
% 0.20/0.53    inference(resolution,[],[f112,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ~v1_relat_1(k1_xboole_0) | spl1_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f110])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ~spl1_8 | spl1_9 | ~spl1_3 | ~spl1_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f99,f66,f61,f114,f110])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_4)),
% 0.20/0.53    inference(forward_demodulation,[],[f98,f68])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f96,f36])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_3),
% 0.20/0.53    inference(superposition,[],[f40,f63])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ~spl1_6 | ~spl1_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f32,f92,f88])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.53    inference(negated_conjecture,[],[f13])).
% 0.20/0.53  fof(f13,conjecture,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    spl1_5 | ~spl1_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f73,f56,f79])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl1_2),
% 0.20/0.53    inference(resolution,[],[f71,f58])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.20/0.53    inference(resolution,[],[f42,f38])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    spl1_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f35,f66])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    spl1_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f34,f61])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    spl1_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f33,f56])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    spl1_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f31,f51])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    v1_relat_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (27904)------------------------------
% 0.20/0.53  % (27904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27904)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (27904)Memory used [KB]: 6268
% 0.20/0.53  % (27904)Time elapsed: 0.091 s
% 0.20/0.53  % (27904)------------------------------
% 0.20/0.53  % (27904)------------------------------
% 0.20/0.53  % (27900)Success in time 0.166 s
%------------------------------------------------------------------------------
