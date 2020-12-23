%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 272 expanded)
%              Number of leaves         :   12 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  237 ( 745 expanded)
%              Number of equality atoms :  114 ( 539 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f889,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f92,f97,f748,f751,f757,f762,f811])).

fof(f811,plain,
    ( spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f810])).

fof(f810,plain,
    ( $false
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f809,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f809,plain,
    ( k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f808,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f808,plain,
    ( sK1 != k2_xboole_0(sK1,k1_xboole_0)
    | spl7_2
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f143,f95])).

fof(f95,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f143,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | spl7_2 ),
    inference(superposition,[],[f82,f60])).

fof(f60,plain,(
    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f82,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_2
  <=> sK1 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f762,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f760,f78])).

fof(f78,plain,
    ( sK1 != sK2
    | spl7_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl7_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f760,plain,
    ( sK1 = sK2
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f86,f81])).

fof(f81,plain,
    ( sK1 = k2_tarski(sK0,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f86,plain,
    ( sK2 = k2_tarski(sK0,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_3
  <=> sK2 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f757,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f173,f755])).

fof(f755,plain,
    ( r2_hidden(sK0,sK2)
    | spl7_5 ),
    inference(subsumption_resolution,[],[f650,f96])).

fof(f96,plain,
    ( k1_xboole_0 != sK2
    | spl7_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f650,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | spl7_5 ),
    inference(superposition,[],[f36,f630])).

fof(f630,plain,
    ( sK0 = sK3(sK2)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f103,f431])).

fof(f431,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | sK0 = X1 ) ),
    inference(resolution,[],[f145,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK1,sK2))
      | sK0 = X0 ) ),
    inference(superposition,[],[f68,f60])).

fof(f68,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f103,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f96,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f173,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_6
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f751,plain,
    ( spl7_3
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f749,f142])).

fof(f142,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | spl7_3 ),
    inference(superposition,[],[f87,f60])).

fof(f87,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f749,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f736,f654])).

fof(f654,plain,
    ( sK0 != sK4(sK0,sK2)
    | spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f651,f39])).

fof(f651,plain,
    ( sK0 != sK4(sK0,k2_xboole_0(sK2,sK2))
    | spl7_3
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f205,f39,f129])).

fof(f129,plain,
    ( ! [X1] :
        ( sK0 != sK4(sK0,X1)
        | sK2 != X1
        | ~ r2_hidden(sK0,X1) )
    | spl7_3 ),
    inference(inner_rewriting,[],[f126])).

fof(f126,plain,
    ( ! [X1] :
        ( sK2 != X1
        | sK0 != sK4(sK0,X1)
        | ~ r2_hidden(sK4(sK0,X1),X1) )
    | spl7_3 ),
    inference(superposition,[],[f87,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k2_tarski(X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f205,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(sK2,X0))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f174,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f174,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f172])).

fof(f736,plain,
    ( sK0 = sK4(sK0,sK2)
    | sK2 = k2_xboole_0(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f734])).

fof(f734,plain,
    ( sK0 = sK4(sK0,sK2)
    | sK2 = k2_xboole_0(sK1,sK2)
    | sK0 = sK4(sK0,sK2) ),
    inference(resolution,[],[f140,f431])).

fof(f140,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0),X0)
      | sK0 = sK4(sK0,X0)
      | k2_xboole_0(sK1,sK2) = X0 ) ),
    inference(superposition,[],[f60,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1)
      | k2_tarski(X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f748,plain,
    ( spl7_2
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f747])).

fof(f747,plain,
    ( $false
    | spl7_2
    | spl7_4 ),
    inference(subsumption_resolution,[],[f746,f143])).

fof(f746,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | spl7_2
    | spl7_4 ),
    inference(subsumption_resolution,[],[f737,f680])).

fof(f680,plain,
    ( sK0 != sK4(sK0,sK1)
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f489,f143,f152])).

fof(f152,plain,(
    ! [X1] :
      ( sK0 != sK4(sK0,X1)
      | k2_xboole_0(sK1,sK2) = X1
      | ~ r2_hidden(sK0,X1) ) ),
    inference(inner_rewriting,[],[f141])).

fof(f141,plain,(
    ! [X1] :
      ( k2_xboole_0(sK1,sK2) = X1
      | sK0 != sK4(sK0,X1)
      | ~ r2_hidden(sK4(sK0,X1),X1) ) ),
    inference(superposition,[],[f60,f64])).

fof(f489,plain,
    ( r2_hidden(sK0,sK1)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f483,f91])).

fof(f91,plain,
    ( k1_xboole_0 != sK1
    | spl7_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f483,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | spl7_4 ),
    inference(superposition,[],[f36,f458])).

fof(f458,plain,
    ( sK0 = sK3(sK1)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f100,f430])).

fof(f430,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(resolution,[],[f145,f72])).

fof(f100,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f91,f36])).

fof(f737,plain,
    ( sK0 = sK4(sK0,sK1)
    | sK1 = k2_xboole_0(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f733])).

fof(f733,plain,
    ( sK0 = sK4(sK0,sK1)
    | sK1 = k2_xboole_0(sK1,sK2)
    | sK0 = sK4(sK0,sK1) ),
    inference(resolution,[],[f140,f430])).

fof(f97,plain,
    ( ~ spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f63,f80,f94])).

fof(f63,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f32,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f62,f89,f85])).

fof(f62,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f74,f80,f76])).

fof(f74,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f61])).

fof(f61,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f34,f44,f44])).

fof(f34,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (6088)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (6079)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (6080)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (6085)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (6083)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (6084)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (6078)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (6087)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (6098)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (6090)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (6104)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (6102)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (6089)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (6097)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (6077)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (6103)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (6101)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (6096)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (6082)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (6076)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (6093)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (6092)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (6086)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (6095)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (6086)Refutation not found, incomplete strategy% (6086)------------------------------
% 0.20/0.54  % (6086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6086)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6086)Memory used [KB]: 10618
% 0.20/0.54  % (6086)Time elapsed: 0.151 s
% 0.20/0.54  % (6086)------------------------------
% 0.20/0.54  % (6086)------------------------------
% 0.20/0.54  % (6081)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (6100)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (6105)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (6094)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (6099)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (6091)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (6085)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f889,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f83,f92,f97,f748,f751,f757,f762,f811])).
% 0.20/0.55  fof(f811,plain,(
% 0.20/0.55    spl7_2 | ~spl7_4 | ~spl7_5),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f810])).
% 0.20/0.55  fof(f810,plain,(
% 0.20/0.55    $false | (spl7_2 | ~spl7_4 | ~spl7_5)),
% 0.20/0.55    inference(subsumption_resolution,[],[f809,f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.55    inference(rectify,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.55  fof(f809,plain,(
% 0.20/0.55    k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_4 | ~spl7_5)),
% 0.20/0.55    inference(forward_demodulation,[],[f808,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl7_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    spl7_4 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.55  fof(f808,plain,(
% 0.20/0.55    sK1 != k2_xboole_0(sK1,k1_xboole_0) | (spl7_2 | ~spl7_5)),
% 0.20/0.55    inference(forward_demodulation,[],[f143,f95])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | ~spl7_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f94])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    spl7_5 <=> k1_xboole_0 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    sK1 != k2_xboole_0(sK1,sK2) | spl7_2),
% 0.20/0.55    inference(superposition,[],[f82,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)),
% 0.20/0.55    inference(definition_unfolding,[],[f35,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.55    inference(negated_conjecture,[],[f25])).
% 0.20/0.55  fof(f25,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    sK1 != k2_tarski(sK0,sK0) | spl7_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    spl7_2 <=> sK1 = k2_tarski(sK0,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.55  fof(f762,plain,(
% 0.20/0.55    spl7_1 | ~spl7_2 | ~spl7_3),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f761])).
% 0.20/0.55  fof(f761,plain,(
% 0.20/0.55    $false | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f760,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    sK1 != sK2 | spl7_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    spl7_1 <=> sK1 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.55  fof(f760,plain,(
% 0.20/0.55    sK1 = sK2 | (~spl7_2 | ~spl7_3)),
% 0.20/0.55    inference(forward_demodulation,[],[f86,f81])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    sK1 = k2_tarski(sK0,sK0) | ~spl7_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f80])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    sK2 = k2_tarski(sK0,sK0) | ~spl7_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f85])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    spl7_3 <=> sK2 = k2_tarski(sK0,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.55  fof(f757,plain,(
% 0.20/0.55    spl7_5 | spl7_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f756])).
% 0.20/0.55  fof(f756,plain,(
% 0.20/0.55    $false | (spl7_5 | spl7_6)),
% 0.20/0.55    inference(subsumption_resolution,[],[f173,f755])).
% 0.20/0.55  fof(f755,plain,(
% 0.20/0.55    r2_hidden(sK0,sK2) | spl7_5),
% 0.20/0.55    inference(subsumption_resolution,[],[f650,f96])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    k1_xboole_0 != sK2 | spl7_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f94])).
% 0.20/0.55  fof(f650,plain,(
% 0.20/0.55    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | spl7_5),
% 0.20/0.55    inference(superposition,[],[f36,f630])).
% 0.20/0.55  fof(f630,plain,(
% 0.20/0.55    sK0 = sK3(sK2) | spl7_5),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f103,f431])).
% 0.20/0.55  fof(f431,plain,(
% 0.20/0.55    ( ! [X1] : (~r2_hidden(X1,sK2) | sK0 = X1) )),
% 0.20/0.55    inference(resolution,[],[f145,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k2_xboole_0(sK1,sK2)) | sK0 = X0) )),
% 0.20/0.55    inference(superposition,[],[f68,f60])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k2_tarski(X0,X0))) )),
% 0.20/0.55    inference(equality_resolution,[],[f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f41,f44])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    r2_hidden(sK3(sK2),sK2) | spl7_5),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f96,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.55  fof(f173,plain,(
% 0.20/0.55    ~r2_hidden(sK0,sK2) | spl7_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f172])).
% 0.20/0.55  fof(f172,plain,(
% 0.20/0.55    spl7_6 <=> r2_hidden(sK0,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.55  fof(f751,plain,(
% 0.20/0.55    spl7_3 | ~spl7_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f750])).
% 0.20/0.55  fof(f750,plain,(
% 0.20/0.55    $false | (spl7_3 | ~spl7_6)),
% 0.20/0.55    inference(subsumption_resolution,[],[f749,f142])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    sK2 != k2_xboole_0(sK1,sK2) | spl7_3),
% 0.20/0.55    inference(superposition,[],[f87,f60])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    sK2 != k2_tarski(sK0,sK0) | spl7_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f85])).
% 0.20/0.55  fof(f749,plain,(
% 0.20/0.55    sK2 = k2_xboole_0(sK1,sK2) | (spl7_3 | ~spl7_6)),
% 0.20/0.55    inference(subsumption_resolution,[],[f736,f654])).
% 0.20/0.55  fof(f654,plain,(
% 0.20/0.55    sK0 != sK4(sK0,sK2) | (spl7_3 | ~spl7_6)),
% 0.20/0.55    inference(forward_demodulation,[],[f651,f39])).
% 0.20/0.55  fof(f651,plain,(
% 0.20/0.55    sK0 != sK4(sK0,k2_xboole_0(sK2,sK2)) | (spl7_3 | ~spl7_6)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f205,f39,f129])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    ( ! [X1] : (sK0 != sK4(sK0,X1) | sK2 != X1 | ~r2_hidden(sK0,X1)) ) | spl7_3),
% 0.20/0.55    inference(inner_rewriting,[],[f126])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    ( ! [X1] : (sK2 != X1 | sK0 != sK4(sK0,X1) | ~r2_hidden(sK4(sK0,X1),X1)) ) | spl7_3),
% 0.20/0.55    inference(superposition,[],[f87,f64])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1) | k2_tarski(X0,X0) = X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f43,f44])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK0,k2_xboole_0(sK2,X0))) ) | ~spl7_6),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f174,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    r2_hidden(sK0,sK2) | ~spl7_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f172])).
% 0.20/0.55  fof(f736,plain,(
% 0.20/0.55    sK0 = sK4(sK0,sK2) | sK2 = k2_xboole_0(sK1,sK2)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f734])).
% 0.20/0.55  fof(f734,plain,(
% 0.20/0.55    sK0 = sK4(sK0,sK2) | sK2 = k2_xboole_0(sK1,sK2) | sK0 = sK4(sK0,sK2)),
% 0.20/0.55    inference(resolution,[],[f140,f431])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK4(sK0,X0),X0) | sK0 = sK4(sK0,X0) | k2_xboole_0(sK1,sK2) = X0) )),
% 0.20/0.55    inference(superposition,[],[f60,f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1) | k2_tarski(X0,X0) = X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f42,f44])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f748,plain,(
% 0.20/0.55    spl7_2 | spl7_4),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f747])).
% 0.20/0.55  fof(f747,plain,(
% 0.20/0.55    $false | (spl7_2 | spl7_4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f746,f143])).
% 0.20/0.55  fof(f746,plain,(
% 0.20/0.55    sK1 = k2_xboole_0(sK1,sK2) | (spl7_2 | spl7_4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f737,f680])).
% 0.20/0.55  fof(f680,plain,(
% 0.20/0.55    sK0 != sK4(sK0,sK1) | (spl7_2 | spl7_4)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f489,f143,f152])).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    ( ! [X1] : (sK0 != sK4(sK0,X1) | k2_xboole_0(sK1,sK2) = X1 | ~r2_hidden(sK0,X1)) )),
% 0.20/0.55    inference(inner_rewriting,[],[f141])).
% 0.20/0.55  fof(f141,plain,(
% 0.20/0.55    ( ! [X1] : (k2_xboole_0(sK1,sK2) = X1 | sK0 != sK4(sK0,X1) | ~r2_hidden(sK4(sK0,X1),X1)) )),
% 0.20/0.55    inference(superposition,[],[f60,f64])).
% 0.20/0.55  fof(f489,plain,(
% 0.20/0.55    r2_hidden(sK0,sK1) | spl7_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f483,f91])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | spl7_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f89])).
% 0.20/0.55  fof(f483,plain,(
% 0.20/0.55    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | spl7_4),
% 0.20/0.55    inference(superposition,[],[f36,f458])).
% 0.20/0.55  fof(f458,plain,(
% 0.20/0.55    sK0 = sK3(sK1) | spl7_4),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f100,f430])).
% 0.20/0.55  fof(f430,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) )),
% 0.20/0.55    inference(resolution,[],[f145,f72])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    r2_hidden(sK3(sK1),sK1) | spl7_4),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f91,f36])).
% 0.20/0.55  fof(f737,plain,(
% 0.20/0.55    sK0 = sK4(sK0,sK1) | sK1 = k2_xboole_0(sK1,sK2)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f733])).
% 0.20/0.55  fof(f733,plain,(
% 0.20/0.55    sK0 = sK4(sK0,sK1) | sK1 = k2_xboole_0(sK1,sK2) | sK0 = sK4(sK0,sK1)),
% 0.20/0.55    inference(resolution,[],[f140,f430])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    ~spl7_5 | ~spl7_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f63,f80,f94])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    sK1 != k2_tarski(sK0,sK0) | k1_xboole_0 != sK2),
% 0.20/0.55    inference(definition_unfolding,[],[f32,f44])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ~spl7_3 | ~spl7_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f62,f89,f85])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | sK2 != k2_tarski(sK0,sK0)),
% 0.20/0.55    inference(definition_unfolding,[],[f33,f44])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    ~spl7_1 | ~spl7_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f74,f80,f76])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    sK1 != k2_tarski(sK0,sK0) | sK1 != sK2),
% 0.20/0.55    inference(inner_rewriting,[],[f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    sK1 != k2_tarski(sK0,sK0) | sK2 != k2_tarski(sK0,sK0)),
% 0.20/0.55    inference(definition_unfolding,[],[f34,f44,f44])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (6085)------------------------------
% 0.20/0.55  % (6085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6085)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (6085)Memory used [KB]: 11001
% 0.20/0.55  % (6085)Time elapsed: 0.158 s
% 0.20/0.55  % (6085)------------------------------
% 0.20/0.55  % (6085)------------------------------
% 0.20/0.56  % (6075)Success in time 0.207 s
%------------------------------------------------------------------------------
