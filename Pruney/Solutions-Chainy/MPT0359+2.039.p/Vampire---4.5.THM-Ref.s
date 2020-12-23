%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 168 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  288 ( 514 expanded)
%              Number of equality atoms :   47 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f65,f73,f83,f106,f126,f131,f142,f155,f160,f181,f186])).

fof(f186,plain,
    ( spl3_11
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f184,f141])).

fof(f141,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_11
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f184,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f182,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f182,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f180,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f180,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_13
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f181,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f171,f76,f54,f178])).

fof(f54,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f76,plain,
    ( spl3_4
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f171,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f78,f135])).

fof(f135,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f78,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f160,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f157,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f157,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_7 ),
    inference(resolution,[],[f99,f51])).

fof(f51,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f99,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_7
  <=> r2_hidden(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f155,plain,
    ( ~ spl3_7
    | spl3_6 ),
    inference(avatar_split_clause,[],[f149,f88,f98])).

fof(f88,plain,
    ( spl3_6
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f149,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | spl3_6 ),
    inference(subsumption_resolution,[],[f144,f32])).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f144,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl3_6 ),
    inference(resolution,[],[f89,f36])).

% (27772)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (27768)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (27782)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (27784)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (27774)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (27764)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (27781)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (27760)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (27780)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f89,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f142,plain,
    ( ~ spl3_11
    | ~ spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f134,f80,f70,f139])).

fof(f70,plain,
    ( spl3_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,
    ( spl3_5
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f134,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f133,f81])).

fof(f81,plain,
    ( sK0 != sK1
    | spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f133,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ spl3_3 ),
    inference(resolution,[],[f72,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f131,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f128,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_10 ),
    inference(resolution,[],[f125,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f125,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK0),sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_10
  <=> r1_tarski(k4_xboole_0(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f126,plain,
    ( ~ spl3_10
    | ~ spl3_6
    | spl3_8 ),
    inference(avatar_split_clause,[],[f116,f103,f88,f123])).

fof(f103,plain,
    ( spl3_8
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f116,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK0),sK0)
    | ~ spl3_6
    | spl3_8 ),
    inference(backward_demodulation,[],[f105,f114])).

fof(f114,plain,
    ( k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f39,f90])).

fof(f90,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f105,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f106,plain,
    ( ~ spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f96,f80,f103])).

fof(f96,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f95,f82])).

fof(f82,plain,
    ( sK0 = sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f95,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f94,f82])).

fof(f94,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f31,f33])).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f31,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f21])).

% (27761)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f21,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f83,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f74,f80,f76])).

fof(f74,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f30,f33])).

fof(f30,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f68,f62,f70])).

fof(f62,plain,
    ( spl3_2
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f68,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f60,f54,f62])).

fof(f60,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f59,f32])).

fof(f59,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f35,f56])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:15:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (27773)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (27766)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (27762)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (27766)Refutation not found, incomplete strategy% (27766)------------------------------
% 0.22/0.54  % (27766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27766)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27766)Memory used [KB]: 10618
% 0.22/0.54  % (27766)Time elapsed: 0.113 s
% 0.22/0.54  % (27766)------------------------------
% 0.22/0.54  % (27766)------------------------------
% 0.22/0.54  % (27762)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f57,f65,f73,f83,f106,f126,f131,f142,f155,f160,f181,f186])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    spl3_11 | ~spl3_13),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f185])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    $false | (spl3_11 | ~spl3_13)),
% 0.22/0.54    inference(subsumption_resolution,[],[f184,f141])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK1) | spl3_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f139])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    spl3_11 <=> r1_tarski(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | ~spl3_13),
% 0.22/0.54    inference(forward_demodulation,[],[f182,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.54    inference(rectify,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    r1_tarski(sK0,k2_xboole_0(sK1,sK1)) | ~spl3_13),
% 0.22/0.54    inference(resolution,[],[f180,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | ~spl3_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f178])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    spl3_13 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    spl3_13 | ~spl3_1 | ~spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f171,f76,f54,f178])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl3_4 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | (~spl3_1 | ~spl3_4)),
% 0.22/0.54    inference(backward_demodulation,[],[f78,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f56,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f54])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f76])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    spl3_7),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f159])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    $false | spl3_7),
% 0.22/0.54    inference(subsumption_resolution,[],[f157,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK0) | spl3_7),
% 0.22/0.54    inference(resolution,[],[f99,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | spl3_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    spl3_7 <=> r2_hidden(sK0,k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    ~spl3_7 | spl3_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f149,f88,f98])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    spl3_6 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | spl3_6),
% 0.22/0.54    inference(subsumption_resolution,[],[f144,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | spl3_6),
% 0.22/0.54    inference(resolution,[],[f89,f36])).
% 0.22/0.55  % (27772)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (27768)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (27782)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.55  % (27784)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.55  % (27774)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (27764)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (27781)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.56  % (27760)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.56  % (27780)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f88])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    ~spl3_11 | ~spl3_3 | spl3_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f134,f80,f70,f139])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    spl3_3 <=> r1_tarski(sK1,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    spl3_5 <=> sK0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK1) | (~spl3_3 | spl3_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f133,f81])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    sK0 != sK1 | spl3_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f80])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK1) | sK0 = sK1 | ~spl3_3),
% 0.22/0.56    inference(resolution,[],[f72,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    r1_tarski(sK1,sK0) | ~spl3_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f70])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    spl3_10),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f130])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    $false | spl3_10),
% 0.22/0.56    inference(subsumption_resolution,[],[f128,f49])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK0) | spl3_10),
% 0.22/0.56    inference(resolution,[],[f125,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    ~r1_tarski(k4_xboole_0(sK0,sK0),sK0) | spl3_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f123])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    spl3_10 <=> r1_tarski(k4_xboole_0(sK0,sK0),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    ~spl3_10 | ~spl3_6 | spl3_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f116,f103,f88,f123])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    spl3_8 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.56  fof(f116,plain,(
% 0.22/0.56    ~r1_tarski(k4_xboole_0(sK0,sK0),sK0) | (~spl3_6 | spl3_8)),
% 0.22/0.56    inference(backward_demodulation,[],[f105,f114])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0) | ~spl3_6),
% 0.22/0.56    inference(resolution,[],[f39,f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f88])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f103])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ~spl3_8 | ~spl3_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f96,f80,f103])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl3_5),
% 0.22/0.56    inference(forward_demodulation,[],[f95,f82])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    sK0 = sK1 | ~spl3_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f80])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_5),
% 0.22/0.56    inference(subsumption_resolution,[],[f94,f82])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f31,f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  % (27761)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(flattening,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.56    inference(negated_conjecture,[],[f10])).
% 0.22/0.56  fof(f10,conjecture,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    spl3_4 | spl3_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f74,f80,f76])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f30,f33])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    spl3_3 | ~spl3_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f68,f62,f70])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    spl3_2 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    r1_tarski(sK1,sK0) | ~spl3_2),
% 0.22/0.56    inference(resolution,[],[f64,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f62])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    spl3_2 | ~spl3_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f60,f54,f62])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.22/0.56    inference(subsumption_resolution,[],[f59,f32])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.22/0.56    inference(resolution,[],[f35,f56])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    spl3_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f29,f54])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (27762)------------------------------
% 0.22/0.56  % (27762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27762)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (27762)Memory used [KB]: 6268
% 0.22/0.56  % (27762)Time elapsed: 0.119 s
% 0.22/0.56  % (27762)------------------------------
% 0.22/0.56  % (27762)------------------------------
% 0.22/0.56  % (27759)Success in time 0.194 s
%------------------------------------------------------------------------------
