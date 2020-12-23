%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:52 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 149 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  216 ( 577 expanded)
%              Number of equality atoms :  144 ( 471 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f77,f81,f85,f92,f128,f129,f131])).

fof(f131,plain,
    ( spl7_1
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f34,plain,
    ( sK1 != sK4
    | spl7_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl7_1
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f127,plain,
    ( sK1 = sK4
    | ~ spl7_7 ),
    inference(resolution,[],[f97,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | X4 = X5 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X0 = X1
        & X2 = X3
        & X4 = X5 )
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X5,X2,X4,X1,X3,X0] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | ~ sP0(X5,X2,X4,X1,X3,X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X5,X2,X4,X1,X3,X0] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | ~ sP0(X5,X2,X4,X1,X3,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (28758)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f97,plain,
    ( sP0(sK3,sK6,sK2,sK5,sK1,sK4)
    | ~ spl7_7 ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK1,sK2,sK3)
        | sP0(X2,sK6,X1,sK5,X0,sK4) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_7
  <=> ! [X1,X0,X2] :
        ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK1,sK2,sK3)
        | sP0(X2,sK6,X1,sK5,X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f129,plain,
    ( spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f126,f70,f36])).

fof(f36,plain,
    ( spl7_2
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f126,plain,
    ( sK2 = sK5
    | ~ spl7_7 ),
    inference(resolution,[],[f97,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f128,plain,
    ( spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f125,f70,f40])).

fof(f40,plain,
    ( spl7_3
  <=> sK3 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f125,plain,
    ( sK3 = sK6
    | ~ spl7_7 ),
    inference(resolution,[],[f97,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,
    ( spl7_7
    | spl7_4
    | spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f91,f66,f62,f58,f70])).

fof(f58,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f62,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f66,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f91,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(sK1,sK2,sK3)
        | sP0(X5,sK6,X4,sK5,X3,sK4) )
    | spl7_4
    | spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f90,f59])).

fof(f59,plain,
    ( k1_xboole_0 != sK4
    | spl7_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f90,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(sK1,sK2,sK3)
        | k1_xboole_0 = sK4
        | sP0(X5,sK6,X4,sK5,X3,sK4) )
    | spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f89,f63])).

fof(f63,plain,
    ( k1_xboole_0 != sK5
    | spl7_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f89,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(sK1,sK2,sK3)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sP0(X5,sK6,X4,sK5,X3,sK4) )
    | spl7_6 ),
    inference(subsumption_resolution,[],[f87,f67])).

fof(f67,plain,
    ( k1_xboole_0 != sK6
    | spl7_6 ),
    inference(avatar_component_clause,[],[f66])).

% (28777)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f87,plain,(
    ! [X4,X5,X3] :
      ( k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(sK1,sK2,sK3)
      | k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4
      | sP0(X5,sK6,X4,sK5,X3,sK4) ) ),
    inference(superposition,[],[f27,f17])).

fof(f17,plain,(
    k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK3 != sK6
      | sK2 != sK5
      | sK1 != sK4 )
    & k1_xboole_0 != k3_zfmisc_1(sK1,sK2,sK3)
    & k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f6,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK3 != sK6
        | sK2 != sK5
        | sK1 != sK4 )
      & k1_xboole_0 != k3_zfmisc_1(sK1,sK2,sK3)
      & k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f5])).

% (28756)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sP0(X5,X2,X4,X1,X3,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP0(X5,X2,X4,X1,X3,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(definition_folding,[],[f8,f9])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f85,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f83,f18])).

fof(f18,plain,(
    k1_xboole_0 != k3_zfmisc_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK1,sK2,sK3)
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f82,f28])).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f82,plain,
    ( k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,sK5,k1_xboole_0)
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f17,f68])).

fof(f68,plain,
    ( k1_xboole_0 = sK6
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f81,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f79,f18])).

fof(f79,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK1,sK2,sK3)
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f78,f29])).

fof(f29,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,
    ( k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,k1_xboole_0,sK6)
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f17,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK5
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f77,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f75,f18])).

fof(f75,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK1,sK2,sK3)
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f73,f30])).

fof(f30,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,
    ( k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(k1_xboole_0,sK5,sK6)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f17,f60])).

fof(f60,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f43,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f19,f40,f36,f32])).

fof(f19,plain,
    ( sK3 != sK6
    | sK2 != sK5
    | sK1 != sK4 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:09:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.19/0.52  % (28755)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.19/0.52  % (28761)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.19/0.52  % (28778)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.19/0.52  % (28763)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.19/0.52  % (28760)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.19/0.52  % (28770)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.19/0.53  % (28768)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.19/0.53  % (28759)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.19/0.53  % (28757)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.34/0.53  % (28774)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.34/0.53  % (28762)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.34/0.53  % (28759)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f132,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f43,f77,f81,f85,f92,f128,f129,f131])).
% 1.34/0.53  fof(f131,plain,(
% 1.34/0.53    spl7_1 | ~spl7_7),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f130])).
% 1.34/0.53  fof(f130,plain,(
% 1.34/0.53    $false | (spl7_1 | ~spl7_7)),
% 1.34/0.53    inference(subsumption_resolution,[],[f127,f34])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    sK1 != sK4 | spl7_1),
% 1.34/0.53    inference(avatar_component_clause,[],[f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    spl7_1 <=> sK1 = sK4),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.34/0.53  fof(f127,plain,(
% 1.34/0.53    sK1 = sK4 | ~spl7_7),
% 1.34/0.53    inference(resolution,[],[f97,f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4,X5) | X4 = X5) )),
% 1.34/0.53    inference(cnf_transformation,[],[f16])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : ((X0 = X1 & X2 = X3 & X4 = X5) | ~sP0(X0,X1,X2,X3,X4,X5))),
% 1.34/0.53    inference(rectify,[],[f15])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    ! [X5,X2,X4,X1,X3,X0] : ((X2 = X5 & X1 = X4 & X0 = X3) | ~sP0(X5,X2,X4,X1,X3,X0))),
% 1.34/0.53    inference(nnf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,plain,(
% 1.34/0.53    ! [X5,X2,X4,X1,X3,X0] : ((X2 = X5 & X1 = X4 & X0 = X3) | ~sP0(X5,X2,X4,X1,X3,X0))),
% 1.34/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.34/0.53  % (28758)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.34/0.53  fof(f97,plain,(
% 1.34/0.53    sP0(sK3,sK6,sK2,sK5,sK1,sK4) | ~spl7_7),
% 1.34/0.53    inference(equality_resolution,[],[f71])).
% 1.34/0.53  fof(f71,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK1,sK2,sK3) | sP0(X2,sK6,X1,sK5,X0,sK4)) ) | ~spl7_7),
% 1.34/0.53    inference(avatar_component_clause,[],[f70])).
% 1.34/0.53  fof(f70,plain,(
% 1.34/0.53    spl7_7 <=> ! [X1,X0,X2] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK1,sK2,sK3) | sP0(X2,sK6,X1,sK5,X0,sK4))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.34/0.53  fof(f129,plain,(
% 1.34/0.53    spl7_2 | ~spl7_7),
% 1.34/0.53    inference(avatar_split_clause,[],[f126,f70,f36])).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    spl7_2 <=> sK2 = sK5),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.34/0.53  fof(f126,plain,(
% 1.34/0.53    sK2 = sK5 | ~spl7_7),
% 1.34/0.53    inference(resolution,[],[f97,f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4,X5) | X2 = X3) )),
% 1.34/0.53    inference(cnf_transformation,[],[f16])).
% 1.34/0.53  fof(f128,plain,(
% 1.34/0.53    spl7_3 | ~spl7_7),
% 1.34/0.53    inference(avatar_split_clause,[],[f125,f70,f40])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    spl7_3 <=> sK3 = sK6),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.34/0.53  fof(f125,plain,(
% 1.34/0.53    sK3 = sK6 | ~spl7_7),
% 1.34/0.53    inference(resolution,[],[f97,f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4,X5) | X0 = X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f16])).
% 1.34/0.53  fof(f92,plain,(
% 1.34/0.53    spl7_7 | spl7_4 | spl7_5 | spl7_6),
% 1.34/0.53    inference(avatar_split_clause,[],[f91,f66,f62,f58,f70])).
% 1.34/0.53  fof(f58,plain,(
% 1.34/0.53    spl7_4 <=> k1_xboole_0 = sK4),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.34/0.53  fof(f62,plain,(
% 1.34/0.53    spl7_5 <=> k1_xboole_0 = sK5),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.34/0.53  fof(f66,plain,(
% 1.34/0.53    spl7_6 <=> k1_xboole_0 = sK6),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.34/0.53  fof(f91,plain,(
% 1.34/0.53    ( ! [X4,X5,X3] : (k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(sK1,sK2,sK3) | sP0(X5,sK6,X4,sK5,X3,sK4)) ) | (spl7_4 | spl7_5 | spl7_6)),
% 1.34/0.53    inference(subsumption_resolution,[],[f90,f59])).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    k1_xboole_0 != sK4 | spl7_4),
% 1.34/0.53    inference(avatar_component_clause,[],[f58])).
% 1.34/0.53  fof(f90,plain,(
% 1.34/0.53    ( ! [X4,X5,X3] : (k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(sK1,sK2,sK3) | k1_xboole_0 = sK4 | sP0(X5,sK6,X4,sK5,X3,sK4)) ) | (spl7_5 | spl7_6)),
% 1.34/0.53    inference(subsumption_resolution,[],[f89,f63])).
% 1.34/0.53  fof(f63,plain,(
% 1.34/0.53    k1_xboole_0 != sK5 | spl7_5),
% 1.34/0.53    inference(avatar_component_clause,[],[f62])).
% 1.34/0.53  fof(f89,plain,(
% 1.34/0.53    ( ! [X4,X5,X3] : (k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(sK1,sK2,sK3) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sP0(X5,sK6,X4,sK5,X3,sK4)) ) | spl7_6),
% 1.34/0.53    inference(subsumption_resolution,[],[f87,f67])).
% 1.34/0.53  fof(f67,plain,(
% 1.34/0.53    k1_xboole_0 != sK6 | spl7_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f66])).
% 1.34/0.53  % (28777)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.34/0.53  fof(f87,plain,(
% 1.34/0.53    ( ! [X4,X5,X3] : (k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(sK1,sK2,sK3) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sP0(X5,sK6,X4,sK5,X3,sK4)) )),
% 1.34/0.53    inference(superposition,[],[f27,f17])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,sK5,sK6)),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,plain,(
% 1.34/0.53    (sK3 != sK6 | sK2 != sK5 | sK1 != sK4) & k1_xboole_0 != k3_zfmisc_1(sK1,sK2,sK3) & k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,sK5,sK6)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f6,f11])).
% 1.34/0.53  fof(f11,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)) => ((sK3 != sK6 | sK2 != sK5 | sK1 != sK4) & k1_xboole_0 != k3_zfmisc_1(sK1,sK2,sK3) & k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,sK5,sK6))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f6,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 1.34/0.53    inference(flattening,[],[f5])).
% 1.34/0.53  % (28756)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.53  fof(f5,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 1.34/0.53    inference(ennf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 1.34/0.53    inference(negated_conjecture,[],[f3])).
% 1.34/0.53  fof(f3,conjecture,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sP0(X5,X2,X4,X1,X3,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : (sP0(X5,X2,X4,X1,X3,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.34/0.53    inference(definition_folding,[],[f8,f9])).
% 1.34/0.53  fof(f8,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.34/0.53    inference(flattening,[],[f7])).
% 1.34/0.53  fof(f7,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.34/0.53    inference(ennf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 1.34/0.53  fof(f85,plain,(
% 1.34/0.53    ~spl7_6),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f84])).
% 1.34/0.53  fof(f84,plain,(
% 1.34/0.53    $false | ~spl7_6),
% 1.34/0.53    inference(subsumption_resolution,[],[f83,f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    k1_xboole_0 != k3_zfmisc_1(sK1,sK2,sK3)),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f83,plain,(
% 1.34/0.53    k1_xboole_0 = k3_zfmisc_1(sK1,sK2,sK3) | ~spl7_6),
% 1.34/0.53    inference(forward_demodulation,[],[f82,f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0)) )),
% 1.34/0.53    inference(equality_resolution,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f14])).
% 1.34/0.53  fof(f14,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.53    inference(flattening,[],[f13])).
% 1.34/0.53  fof(f13,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.34/0.53    inference(nnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.34/0.53  fof(f82,plain,(
% 1.34/0.53    k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,sK5,k1_xboole_0) | ~spl7_6),
% 1.34/0.53    inference(forward_demodulation,[],[f17,f68])).
% 1.34/0.53  fof(f68,plain,(
% 1.34/0.53    k1_xboole_0 = sK6 | ~spl7_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f66])).
% 1.34/0.53  fof(f81,plain,(
% 1.34/0.53    ~spl7_5),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f80])).
% 1.34/0.53  fof(f80,plain,(
% 1.34/0.53    $false | ~spl7_5),
% 1.34/0.53    inference(subsumption_resolution,[],[f79,f18])).
% 1.34/0.53  fof(f79,plain,(
% 1.34/0.53    k1_xboole_0 = k3_zfmisc_1(sK1,sK2,sK3) | ~spl7_5),
% 1.34/0.53    inference(forward_demodulation,[],[f78,f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ( ! [X2,X0] : (k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2)) )),
% 1.34/0.53    inference(equality_resolution,[],[f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f14])).
% 1.34/0.53  fof(f78,plain,(
% 1.34/0.53    k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(sK4,k1_xboole_0,sK6) | ~spl7_5),
% 1.34/0.53    inference(forward_demodulation,[],[f17,f64])).
% 1.34/0.53  fof(f64,plain,(
% 1.34/0.53    k1_xboole_0 = sK5 | ~spl7_5),
% 1.34/0.53    inference(avatar_component_clause,[],[f62])).
% 1.34/0.53  fof(f77,plain,(
% 1.34/0.53    ~spl7_4),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f76])).
% 1.34/0.53  fof(f76,plain,(
% 1.34/0.53    $false | ~spl7_4),
% 1.34/0.53    inference(subsumption_resolution,[],[f75,f18])).
% 1.34/0.53  fof(f75,plain,(
% 1.34/0.53    k1_xboole_0 = k3_zfmisc_1(sK1,sK2,sK3) | ~spl7_4),
% 1.34/0.53    inference(forward_demodulation,[],[f73,f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ( ! [X2,X1] : (k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2)) )),
% 1.34/0.53    inference(equality_resolution,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f14])).
% 1.34/0.53  fof(f73,plain,(
% 1.34/0.53    k3_zfmisc_1(sK1,sK2,sK3) = k3_zfmisc_1(k1_xboole_0,sK5,sK6) | ~spl7_4),
% 1.34/0.53    inference(backward_demodulation,[],[f17,f60])).
% 1.34/0.53  fof(f60,plain,(
% 1.34/0.53    k1_xboole_0 = sK4 | ~spl7_4),
% 1.34/0.53    inference(avatar_component_clause,[],[f58])).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 1.34/0.53    inference(avatar_split_clause,[],[f19,f40,f36,f32])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    sK3 != sK6 | sK2 != sK5 | sK1 != sK4),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (28759)------------------------------
% 1.34/0.53  % (28759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (28759)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (28759)Memory used [KB]: 6140
% 1.34/0.53  % (28759)Time elapsed: 0.091 s
% 1.34/0.54  % (28759)------------------------------
% 1.34/0.54  % (28759)------------------------------
% 1.34/0.54  % (28761)Refutation not found, incomplete strategy% (28761)------------------------------
% 1.34/0.54  % (28761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (28761)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (28761)Memory used [KB]: 10618
% 1.34/0.54  % (28761)Time elapsed: 0.120 s
% 1.34/0.54  % (28761)------------------------------
% 1.34/0.54  % (28761)------------------------------
% 1.34/0.54  % (28754)Success in time 0.169 s
%------------------------------------------------------------------------------
