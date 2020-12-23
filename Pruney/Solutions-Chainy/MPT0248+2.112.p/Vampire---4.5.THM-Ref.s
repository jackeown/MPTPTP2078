%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 313 expanded)
%              Number of leaves         :   12 (  92 expanded)
%              Depth                    :   17
%              Number of atoms          :  242 (1247 expanded)
%              Number of equality atoms :  144 (1035 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f79,f104,f163,f198,f215])).

fof(f215,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f206,f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f206,plain,
    ( k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(backward_demodulation,[],[f167,f65])).

fof(f65,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f167,plain,
    ( sK2 != k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_3
    | spl3_4 ),
    inference(superposition,[],[f78,f166])).

fof(f166,plain,
    ( k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f39,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f39,plain,(
    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f78,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_4
  <=> sK2 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f198,plain,
    ( spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f196,f167])).

fof(f196,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,sK2)
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f192,f66])).

fof(f66,plain,
    ( k1_xboole_0 != sK2
    | spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f192,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f188,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

% (15329)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f188,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | k1_xboole_0 = X0
        | k2_xboole_0(k1_xboole_0,sK2) = X0 )
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f97,f73])).

fof(f97,plain,(
    ! [X0] :
      ( k2_xboole_0(sK1,sK2) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f58,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
      | k2_xboole_0(sK1,sK2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
      | k2_xboole_0(sK1,sK2) = X0
      | k2_xboole_0(sK1,sK2) = X0
      | k1_xboole_0 = X0
      | k2_xboole_0(sK1,sK2) = X0 ) ),
    inference(superposition,[],[f42,f39])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f24,f33,f33])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f163,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f162])).

% (15330)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (15333)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (15331)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (15351)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (15348)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (15335)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (15345)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f162,plain,
    ( $false
    | spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f161,f127])).

fof(f127,plain,
    ( sK1 != sK2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f50,f106])).

fof(f106,plain,
    ( sK1 = k2_tarski(sK0,sK0)
    | spl3_3 ),
    inference(backward_demodulation,[],[f39,f105])).

fof(f105,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f98,f74])).

fof(f74,plain,
    ( k1_xboole_0 != sK1
    | spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f98,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f50,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f49])).

fof(f49,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f38])).

fof(f38,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | sK1 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f21,f33,f33])).

fof(f21,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f161,plain,
    ( sK1 = sK2
    | spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f157,f66])).

fof(f157,plain,
    ( k1_xboole_0 = sK2
    | sK1 = sK2
    | spl3_3 ),
    inference(resolution,[],[f139,f47])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | k1_xboole_0 = X0
        | sK1 = X0 )
    | spl3_3 ),
    inference(resolution,[],[f114,f113])).

fof(f113,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,sK2) )
    | spl3_3 ),
    inference(superposition,[],[f34,f105])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | spl3_3 ),
    inference(forward_demodulation,[],[f110,f105])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k2_xboole_0(sK1,sK2) = X0
        | k1_xboole_0 = X0 )
    | spl3_3 ),
    inference(backward_demodulation,[],[f58,f105])).

fof(f104,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f102,f74])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | spl3_1 ),
    inference(subsumption_resolution,[],[f98,f68])).

fof(f68,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | spl3_1 ),
    inference(superposition,[],[f62,f39])).

fof(f62,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_1
  <=> sK1 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f37,f76,f72])).

fof(f37,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f22,f33])).

fof(f22,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f36,f64,f60])).

fof(f36,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f23,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:40:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (15334)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (15353)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (15342)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (15344)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (15336)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (15358)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (15358)Refutation not found, incomplete strategy% (15358)------------------------------
% 0.21/0.52  % (15358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15358)Memory used [KB]: 1663
% 0.21/0.52  % (15358)Time elapsed: 0.115 s
% 0.21/0.52  % (15358)------------------------------
% 0.21/0.52  % (15358)------------------------------
% 0.21/0.52  % (15332)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (15353)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f67,f79,f104,f163,f198,f215])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    ~spl3_2 | ~spl3_3 | spl3_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f214])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    $false | (~spl3_2 | ~spl3_3 | spl3_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f206,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | spl3_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f167,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl3_2 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    sK2 != k2_xboole_0(k1_xboole_0,sK2) | (~spl3_3 | spl3_4)),
% 0.21/0.52    inference(superposition,[],[f78,f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2) | ~spl3_3),
% 0.21/0.52    inference(forward_demodulation,[],[f39,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl3_3 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    sK2 != k2_tarski(sK0,sK0) | spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl3_4 <=> sK2 = k2_tarski(sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    spl3_2 | ~spl3_3 | spl3_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    $false | (spl3_2 | ~spl3_3 | spl3_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f196,f167])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    sK2 = k2_xboole_0(k1_xboole_0,sK2) | (spl3_2 | ~spl3_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f192,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    k1_xboole_0 != sK2 | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f64])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | sK2 = k2_xboole_0(k1_xboole_0,sK2) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f188,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  % (15329)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,sK2) | k1_xboole_0 = X0 | k2_xboole_0(k1_xboole_0,sK2) = X0) ) | ~spl3_3),
% 0.21/0.52    inference(forward_demodulation,[],[f97,f73])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f58,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X0 | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0 | k2_xboole_0(sK1,sK2) = X0) )),
% 0.21/0.52    inference(superposition,[],[f42,f39])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f33,f33])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl3_2 | spl3_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.52  % (15330)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (15333)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (15331)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (15351)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (15348)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (15335)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15345)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    $false | (spl3_2 | spl3_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f161,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    sK1 != sK2 | spl3_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    sK1 = k2_tarski(sK0,sK0) | spl3_3),
% 0.21/0.53    inference(backward_demodulation,[],[f39,f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK1,sK2) | spl3_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f72])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f58,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    sK1 != k2_tarski(sK0,sK0) | sK1 != sK2),
% 0.21/0.53    inference(inner_rewriting,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    sK2 != k2_tarski(sK0,sK0) | sK1 != sK2),
% 0.21/0.53    inference(inner_rewriting,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    sK2 != k2_tarski(sK0,sK0) | sK1 != k2_tarski(sK0,sK0)),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f33,f33])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    sK1 = sK2 | (spl3_2 | spl3_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f157,f66])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | sK1 = sK2 | spl3_3),
% 0.21/0.53    inference(resolution,[],[f139,f47])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK2) | k1_xboole_0 = X0 | sK1 = X0) ) | spl3_3),
% 0.21/0.53    inference(resolution,[],[f114,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,sK1) | ~r1_tarski(X0,sK2)) ) | spl3_3),
% 0.21/0.53    inference(superposition,[],[f34,f105])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | spl3_3),
% 0.21/0.53    inference(forward_demodulation,[],[f110,f105])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK1) | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) ) | spl3_3),
% 0.21/0.53    inference(backward_demodulation,[],[f58,f105])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl3_1 | spl3_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    $false | (spl3_1 | spl3_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f102,f74])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | spl3_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    sK1 != k2_xboole_0(sK1,sK2) | spl3_1),
% 0.21/0.53    inference(superposition,[],[f62,f39])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    sK1 != k2_tarski(sK0,sK0) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl3_1 <=> sK1 = k2_tarski(sK0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ~spl3_3 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f76,f72])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    sK2 != k2_tarski(sK0,sK0) | k1_xboole_0 != sK1),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f33])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f64,f60])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    k1_xboole_0 != sK2 | sK1 != k2_tarski(sK0,sK0)),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f33])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (15353)------------------------------
% 0.21/0.53  % (15353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15353)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (15353)Memory used [KB]: 10746
% 0.21/0.53  % (15353)Time elapsed: 0.067 s
% 0.21/0.53  % (15353)------------------------------
% 0.21/0.53  % (15353)------------------------------
% 0.21/0.53  % (15345)Refutation not found, incomplete strategy% (15345)------------------------------
% 0.21/0.53  % (15345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15345)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15345)Memory used [KB]: 10618
% 0.21/0.53  % (15345)Time elapsed: 0.128 s
% 0.21/0.53  % (15345)------------------------------
% 0.21/0.53  % (15345)------------------------------
% 0.21/0.53  % (15349)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.47/0.54  % (15340)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.47/0.54  % (15338)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.47/0.54  % (15328)Success in time 0.18 s
%------------------------------------------------------------------------------
