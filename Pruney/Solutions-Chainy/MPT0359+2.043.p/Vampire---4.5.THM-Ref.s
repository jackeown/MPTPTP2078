%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:44 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 186 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  297 ( 531 expanded)
%              Number of equality atoms :   71 ( 140 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f79,f93,f135,f163,f183,f198,f214,f254,f259,f319])).

fof(f319,plain,
    ( ~ spl3_17
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl3_17
    | spl3_18 ),
    inference(subsumption_resolution,[],[f311,f290])).

fof(f290,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f258,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f258,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl3_18
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f311,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_17 ),
    inference(superposition,[],[f253,f101])).

fof(f101,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f253,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl3_17
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f259,plain,
    ( ~ spl3_18
    | spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f234,f211,f76,f256])).

fof(f76,plain,
    ( spl3_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f211,plain,
    ( spl3_12
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f234,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f77,f213,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f213,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f211])).

fof(f77,plain,
    ( sK0 != sK1
    | spl3_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f254,plain,
    ( spl3_17
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f184,f180,f251])).

fof(f180,plain,
    ( spl3_9
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

% (16182)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f184,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f182,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f182,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f180])).

fof(f214,plain,
    ( spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f202,f195,f211])).

fof(f195,plain,
    ( spl3_10
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f202,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f197,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f197,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f195])).

fof(f198,plain,
    ( spl3_10
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f153,f65,f195])).

fof(f65,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f153,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f34,f67,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f67,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f183,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f156,f72,f65,f180])).

fof(f72,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f156,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f74,f152])).

fof(f152,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f67,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

% (16180)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f74,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f163,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f161,f34])).

fof(f161,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(subsumption_resolution,[],[f158,f94])).

fof(f94,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f57,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f158,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(resolution,[],[f86,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_4
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f135,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f132,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f70,f48])).

% (16192)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f70,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f38,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f56,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

% (16184)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f132,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_4
    | spl3_5 ),
    inference(backward_demodulation,[],[f112,f130])).

fof(f130,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f127,f63])).

fof(f127,plain,
    ( k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f87,f44])).

fof(f87,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f112,plain,
    ( k1_xboole_0 != k4_xboole_0(k3_subset_1(sK0,sK0),sK0)
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f92,f54])).

fof(f92,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_5
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

% (16193)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f93,plain,
    ( ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f82,f76,f90])).

fof(f82,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f81,f78])).

fof(f78,plain,
    ( sK0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f81,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | sK0 != sK1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f62,f78])).

fof(f62,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f33,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f33,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f79,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f61,f76,f72])).

fof(f61,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f32,f35])).

fof(f32,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n022.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 12:34:10 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.12/0.43  % (16200)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.12/0.44  % (16194)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.12/0.45  % (16194)Refutation not found, incomplete strategy% (16194)------------------------------
% 0.12/0.45  % (16194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.45  % (16194)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.45  
% 0.12/0.45  % (16194)Memory used [KB]: 1791
% 0.12/0.45  % (16194)Time elapsed: 0.049 s
% 0.12/0.45  % (16194)------------------------------
% 0.12/0.45  % (16194)------------------------------
% 0.12/0.45  % (16181)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.12/0.45  % (16186)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.45  % (16200)Refutation found. Thanks to Tanya!
% 0.12/0.45  % SZS status Theorem for theBenchmark
% 0.12/0.45  % (16185)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.12/0.45  % SZS output start Proof for theBenchmark
% 0.12/0.45  fof(f320,plain,(
% 0.12/0.45    $false),
% 0.12/0.45    inference(avatar_sat_refutation,[],[f68,f79,f93,f135,f163,f183,f198,f214,f254,f259,f319])).
% 0.12/0.45  fof(f319,plain,(
% 0.12/0.45    ~spl3_17 | spl3_18),
% 0.12/0.45    inference(avatar_contradiction_clause,[],[f318])).
% 0.12/0.45  fof(f318,plain,(
% 0.12/0.45    $false | (~spl3_17 | spl3_18)),
% 0.12/0.45    inference(subsumption_resolution,[],[f311,f290])).
% 0.12/0.45  fof(f290,plain,(
% 0.12/0.45    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_18),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f258,f54])).
% 0.12/0.45  fof(f54,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f30])).
% 0.12/0.45  fof(f30,plain,(
% 0.12/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.12/0.45    inference(nnf_transformation,[],[f2])).
% 0.12/0.45  fof(f2,axiom,(
% 0.12/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.12/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.12/0.45  fof(f258,plain,(
% 0.12/0.45    ~r1_tarski(sK0,sK1) | spl3_18),
% 0.12/0.45    inference(avatar_component_clause,[],[f256])).
% 0.12/0.45  fof(f256,plain,(
% 0.12/0.45    spl3_18 <=> r1_tarski(sK0,sK1)),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.12/0.45  fof(f311,plain,(
% 0.12/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_17),
% 0.12/0.45    inference(superposition,[],[f253,f101])).
% 0.12/0.45  fof(f101,plain,(
% 0.12/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f38,f48])).
% 0.12/0.45  fof(f48,plain,(
% 0.12/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.12/0.45    inference(cnf_transformation,[],[f25])).
% 0.12/0.45  fof(f25,plain,(
% 0.12/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.12/0.45    inference(nnf_transformation,[],[f7])).
% 0.12/0.45  fof(f7,axiom,(
% 0.12/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.12/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.12/0.45  fof(f38,plain,(
% 0.12/0.45    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f6])).
% 0.12/0.45  fof(f6,axiom,(
% 0.12/0.45    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.12/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.12/0.45  fof(f253,plain,(
% 0.12/0.45    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) | ~spl3_17),
% 0.12/0.45    inference(avatar_component_clause,[],[f251])).
% 0.12/0.45  fof(f251,plain,(
% 0.12/0.45    spl3_17 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.12/0.45  fof(f259,plain,(
% 0.12/0.45    ~spl3_18 | spl3_3 | ~spl3_12),
% 0.12/0.45    inference(avatar_split_clause,[],[f234,f211,f76,f256])).
% 0.12/0.45  fof(f76,plain,(
% 0.12/0.45    spl3_3 <=> sK0 = sK1),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.12/0.45  fof(f211,plain,(
% 0.12/0.45    spl3_12 <=> r1_tarski(sK1,sK0)),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.12/0.45  fof(f234,plain,(
% 0.12/0.45    ~r1_tarski(sK0,sK1) | (spl3_3 | ~spl3_12)),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f77,f213,f47])).
% 0.12/0.45  fof(f47,plain,(
% 0.12/0.45    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f24])).
% 0.12/0.45  fof(f24,plain,(
% 0.12/0.45    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.12/0.45    inference(flattening,[],[f23])).
% 0.12/0.45  fof(f23,plain,(
% 0.12/0.45    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.12/0.45    inference(nnf_transformation,[],[f1])).
% 0.12/0.45  fof(f1,axiom,(
% 0.12/0.45    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.12/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.12/0.45  fof(f213,plain,(
% 0.12/0.45    r1_tarski(sK1,sK0) | ~spl3_12),
% 0.12/0.45    inference(avatar_component_clause,[],[f211])).
% 0.12/0.45  fof(f77,plain,(
% 0.12/0.45    sK0 != sK1 | spl3_3),
% 0.12/0.45    inference(avatar_component_clause,[],[f76])).
% 0.12/0.45  fof(f254,plain,(
% 0.12/0.45    spl3_17 | ~spl3_9),
% 0.12/0.45    inference(avatar_split_clause,[],[f184,f180,f251])).
% 0.12/0.45  fof(f180,plain,(
% 0.12/0.45    spl3_9 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.12/0.45  % (16182)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.12/0.45  fof(f184,plain,(
% 0.12/0.45    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) | ~spl3_9),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f182,f55])).
% 0.12/0.45  fof(f55,plain,(
% 0.12/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.12/0.45    inference(cnf_transformation,[],[f30])).
% 0.12/0.45  fof(f182,plain,(
% 0.12/0.45    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | ~spl3_9),
% 0.12/0.45    inference(avatar_component_clause,[],[f180])).
% 0.12/0.45  fof(f214,plain,(
% 0.12/0.45    spl3_12 | ~spl3_10),
% 0.12/0.45    inference(avatar_split_clause,[],[f202,f195,f211])).
% 0.12/0.45  fof(f195,plain,(
% 0.12/0.45    spl3_10 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.12/0.45  fof(f202,plain,(
% 0.12/0.45    r1_tarski(sK1,sK0) | ~spl3_10),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f197,f60])).
% 0.12/0.45  fof(f60,plain,(
% 0.12/0.45    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.12/0.45    inference(equality_resolution,[],[f50])).
% 0.12/0.45  fof(f50,plain,(
% 0.12/0.45    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.12/0.45    inference(cnf_transformation,[],[f29])).
% 0.12/0.45  fof(f29,plain,(
% 0.12/0.45    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.12/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.12/0.45  fof(f28,plain,(
% 0.12/0.45    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.12/0.45    introduced(choice_axiom,[])).
% 0.12/0.45  fof(f27,plain,(
% 0.12/0.45    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.12/0.45    inference(rectify,[],[f26])).
% 0.12/0.45  fof(f26,plain,(
% 0.12/0.45    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.12/0.45    inference(nnf_transformation,[],[f8])).
% 0.12/0.45  fof(f8,axiom,(
% 0.12/0.45    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.12/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.12/0.45  fof(f197,plain,(
% 0.12/0.45    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_10),
% 0.12/0.45    inference(avatar_component_clause,[],[f195])).
% 0.12/0.45  fof(f198,plain,(
% 0.12/0.45    spl3_10 | ~spl3_1),
% 0.12/0.45    inference(avatar_split_clause,[],[f153,f65,f195])).
% 0.12/0.45  fof(f65,plain,(
% 0.12/0.45    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.12/0.45  fof(f153,plain,(
% 0.12/0.45    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f34,f67,f40])).
% 0.12/0.45  fof(f40,plain,(
% 0.12/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f22])).
% 0.12/0.45  fof(f22,plain,(
% 0.12/0.45    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.12/0.45    inference(nnf_transformation,[],[f16])).
% 0.12/0.45  fof(f16,plain,(
% 0.12/0.45    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.12/0.45    inference(ennf_transformation,[],[f9])).
% 0.12/0.45  fof(f9,axiom,(
% 0.12/0.45    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.12/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.12/0.45  fof(f67,plain,(
% 0.12/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.12/0.45    inference(avatar_component_clause,[],[f65])).
% 0.12/0.45  fof(f34,plain,(
% 0.12/0.45    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.12/0.45    inference(cnf_transformation,[],[f12])).
% 0.12/0.45  fof(f12,axiom,(
% 0.12/0.45    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.12/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.12/0.45  fof(f183,plain,(
% 0.12/0.45    spl3_9 | ~spl3_1 | ~spl3_2),
% 0.12/0.45    inference(avatar_split_clause,[],[f156,f72,f65,f180])).
% 0.12/0.45  fof(f72,plain,(
% 0.12/0.45    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.12/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.12/0.45  fof(f156,plain,(
% 0.12/0.45    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | (~spl3_1 | ~spl3_2)),
% 0.12/0.45    inference(backward_demodulation,[],[f74,f152])).
% 0.12/0.45  fof(f152,plain,(
% 0.12/0.45    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f67,f44])).
% 0.12/0.45  fof(f44,plain,(
% 0.12/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.12/0.45    inference(cnf_transformation,[],[f17])).
% 0.12/0.45  % (16180)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.12/0.45  fof(f17,plain,(
% 0.12/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.12/0.45    inference(ennf_transformation,[],[f11])).
% 0.12/0.45  fof(f11,axiom,(
% 0.12/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.12/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.12/0.45  fof(f74,plain,(
% 0.12/0.45    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_2),
% 0.12/0.45    inference(avatar_component_clause,[],[f72])).
% 0.12/0.45  fof(f163,plain,(
% 0.12/0.45    spl3_4),
% 0.12/0.45    inference(avatar_contradiction_clause,[],[f162])).
% 0.12/0.45  fof(f162,plain,(
% 0.12/0.45    $false | spl3_4),
% 0.12/0.45    inference(subsumption_resolution,[],[f161,f34])).
% 0.12/0.45  fof(f161,plain,(
% 0.12/0.45    v1_xboole_0(k1_zfmisc_1(sK0)) | spl3_4),
% 0.12/0.45    inference(subsumption_resolution,[],[f158,f94])).
% 0.12/0.45  fof(f94,plain,(
% 0.12/0.45    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.12/0.45    inference(unit_resulting_resolution,[],[f57,f59])).
% 0.12/0.45  fof(f59,plain,(
% 0.12/0.45    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.12/0.45    inference(equality_resolution,[],[f51])).
% 0.12/0.46  fof(f51,plain,(
% 0.12/0.46    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.12/0.46    inference(cnf_transformation,[],[f29])).
% 0.12/0.46  fof(f57,plain,(
% 0.12/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.12/0.46    inference(equality_resolution,[],[f46])).
% 0.12/0.46  fof(f46,plain,(
% 0.12/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.12/0.46    inference(cnf_transformation,[],[f24])).
% 0.12/0.46  fof(f158,plain,(
% 0.12/0.46    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | spl3_4),
% 0.12/0.46    inference(resolution,[],[f86,f41])).
% 0.12/0.46  fof(f41,plain,(
% 0.12/0.46    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.12/0.46    inference(cnf_transformation,[],[f22])).
% 0.12/0.46  fof(f86,plain,(
% 0.12/0.46    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_4),
% 0.12/0.46    inference(avatar_component_clause,[],[f85])).
% 0.12/0.46  fof(f85,plain,(
% 0.12/0.46    spl3_4 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.12/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.12/0.46  fof(f135,plain,(
% 0.12/0.46    ~spl3_4 | spl3_5),
% 0.12/0.46    inference(avatar_contradiction_clause,[],[f134])).
% 0.12/0.46  fof(f134,plain,(
% 0.12/0.46    $false | (~spl3_4 | spl3_5)),
% 0.12/0.46    inference(subsumption_resolution,[],[f132,f103])).
% 0.12/0.46  fof(f103,plain,(
% 0.12/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.12/0.46    inference(unit_resulting_resolution,[],[f70,f48])).
% 0.12/0.46  % (16192)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.12/0.46  fof(f70,plain,(
% 0.12/0.46    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.12/0.46    inference(superposition,[],[f38,f63])).
% 0.12/0.46  fof(f63,plain,(
% 0.12/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.12/0.46    inference(backward_demodulation,[],[f56,f37])).
% 0.12/0.46  fof(f37,plain,(
% 0.12/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.12/0.46    inference(cnf_transformation,[],[f4])).
% 0.12/0.46  fof(f4,axiom,(
% 0.12/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.12/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.12/0.46  fof(f56,plain,(
% 0.12/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.12/0.46    inference(definition_unfolding,[],[f36,f39])).
% 0.12/0.46  fof(f39,plain,(
% 0.12/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.12/0.46    inference(cnf_transformation,[],[f5])).
% 0.12/0.46  % (16184)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.12/0.46  fof(f5,axiom,(
% 0.12/0.46    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.12/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.12/0.46  fof(f36,plain,(
% 0.12/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.12/0.46    inference(cnf_transformation,[],[f3])).
% 0.12/0.46  fof(f3,axiom,(
% 0.12/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.12/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.12/0.46  fof(f132,plain,(
% 0.12/0.46    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0) | (~spl3_4 | spl3_5)),
% 0.12/0.46    inference(backward_demodulation,[],[f112,f130])).
% 0.12/0.46  fof(f130,plain,(
% 0.12/0.46    k1_xboole_0 = k3_subset_1(sK0,sK0) | ~spl3_4),
% 0.12/0.46    inference(forward_demodulation,[],[f127,f63])).
% 0.12/0.46  fof(f127,plain,(
% 0.12/0.46    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0) | ~spl3_4),
% 0.12/0.46    inference(unit_resulting_resolution,[],[f87,f44])).
% 0.12/0.46  fof(f87,plain,(
% 0.12/0.46    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.12/0.46    inference(avatar_component_clause,[],[f85])).
% 0.12/0.46  fof(f112,plain,(
% 0.12/0.46    k1_xboole_0 != k4_xboole_0(k3_subset_1(sK0,sK0),sK0) | spl3_5),
% 0.12/0.46    inference(unit_resulting_resolution,[],[f92,f54])).
% 0.12/0.46  fof(f92,plain,(
% 0.12/0.46    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_5),
% 0.12/0.46    inference(avatar_component_clause,[],[f90])).
% 0.12/0.46  fof(f90,plain,(
% 0.12/0.46    spl3_5 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.12/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.12/0.46  % (16193)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.12/0.46  fof(f93,plain,(
% 0.12/0.46    ~spl3_5 | ~spl3_3),
% 0.12/0.46    inference(avatar_split_clause,[],[f82,f76,f90])).
% 0.12/0.46  fof(f82,plain,(
% 0.12/0.46    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl3_3),
% 0.12/0.46    inference(subsumption_resolution,[],[f81,f78])).
% 0.12/0.46  fof(f78,plain,(
% 0.12/0.46    sK0 = sK1 | ~spl3_3),
% 0.12/0.46    inference(avatar_component_clause,[],[f76])).
% 0.12/0.46  fof(f81,plain,(
% 0.12/0.46    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | sK0 != sK1 | ~spl3_3),
% 0.12/0.46    inference(backward_demodulation,[],[f62,f78])).
% 0.12/0.46  fof(f62,plain,(
% 0.12/0.46    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.12/0.46    inference(backward_demodulation,[],[f33,f35])).
% 0.12/0.46  fof(f35,plain,(
% 0.12/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.12/0.46    inference(cnf_transformation,[],[f10])).
% 0.12/0.46  fof(f10,axiom,(
% 0.12/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.12/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.12/0.46  fof(f33,plain,(
% 0.12/0.46    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.12/0.46    inference(cnf_transformation,[],[f21])).
% 0.12/0.46  fof(f21,plain,(
% 0.12/0.46    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.12/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 0.12/0.46  fof(f20,plain,(
% 0.12/0.46    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.12/0.46    introduced(choice_axiom,[])).
% 0.12/0.46  fof(f19,plain,(
% 0.12/0.46    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.12/0.46    inference(flattening,[],[f18])).
% 0.12/0.46  fof(f18,plain,(
% 0.12/0.46    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.12/0.46    inference(nnf_transformation,[],[f15])).
% 0.12/0.46  fof(f15,plain,(
% 0.12/0.46    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.12/0.46    inference(ennf_transformation,[],[f14])).
% 0.12/0.46  fof(f14,negated_conjecture,(
% 0.12/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.12/0.46    inference(negated_conjecture,[],[f13])).
% 0.12/0.46  fof(f13,conjecture,(
% 0.12/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.12/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.12/0.46  fof(f79,plain,(
% 0.12/0.46    spl3_2 | spl3_3),
% 0.12/0.46    inference(avatar_split_clause,[],[f61,f76,f72])).
% 0.12/0.46  fof(f61,plain,(
% 0.12/0.46    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.12/0.46    inference(backward_demodulation,[],[f32,f35])).
% 0.12/0.46  fof(f32,plain,(
% 0.12/0.46    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.12/0.46    inference(cnf_transformation,[],[f21])).
% 0.12/0.46  fof(f68,plain,(
% 0.12/0.46    spl3_1),
% 0.12/0.46    inference(avatar_split_clause,[],[f31,f65])).
% 0.12/0.46  fof(f31,plain,(
% 0.12/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.12/0.46    inference(cnf_transformation,[],[f21])).
% 0.12/0.46  % SZS output end Proof for theBenchmark
% 0.12/0.46  % (16200)------------------------------
% 0.12/0.46  % (16200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.46  % (16200)Termination reason: Refutation
% 0.12/0.46  
% 0.12/0.46  % (16200)Memory used [KB]: 10874
% 0.12/0.46  % (16200)Time elapsed: 0.053 s
% 0.12/0.46  % (16200)------------------------------
% 0.12/0.46  % (16200)------------------------------
% 0.12/0.46  % (16192)Refutation not found, incomplete strategy% (16192)------------------------------
% 0.12/0.46  % (16192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.46  % (16192)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.46  
% 0.12/0.46  % (16192)Memory used [KB]: 10618
% 0.12/0.46  % (16192)Time elapsed: 0.118 s
% 0.12/0.46  % (16192)------------------------------
% 0.12/0.46  % (16192)------------------------------
% 0.12/0.46  % (16188)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.12/0.46  % (16190)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.12/0.46  % (16179)Success in time 0.172 s
%------------------------------------------------------------------------------
