%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 290 expanded)
%              Number of leaves         :   10 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  210 (1172 expanded)
%              Number of equality atoms :  170 (1127 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f66,f68,f70,f83,f85])).

fof(f85,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f34,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f63,f30])).

fof(f30,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f63,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f62,f30])).

fof(f62,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f61,f30])).

fof(f61,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2),sK3)
    | k1_xboole_0 != sK0 ),
    inference(inner_rewriting,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f13,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f13,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 )
    & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
      & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f34,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f83,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f81,f60])).

fof(f60,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f59,f30])).

fof(f59,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 != sK1 ),
    inference(forward_demodulation,[],[f58,f30])).

fof(f58,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | k1_xboole_0 != sK1 ),
    inference(forward_demodulation,[],[f57,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2),sK3)
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f14,f23])).

fof(f14,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f80,f64])).

fof(f80,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(superposition,[],[f18,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f76,f56])).

fof(f56,plain,(
    k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f55,f30])).

fof(f55,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 != sK2 ),
    inference(forward_demodulation,[],[f54,f29])).

fof(f54,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3)
    | k1_xboole_0 != sK2 ),
    inference(inner_rewriting,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f15,f23])).

fof(f15,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(superposition,[],[f18,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f72,f53])).

fof(f53,plain,(
    k1_xboole_0 != sK3 ),
    inference(subsumption_resolution,[],[f52,f29])).

fof(f52,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | k1_xboole_0 != sK3 ),
    inference(inner_rewriting,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f16,f23])).

fof(f16,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(superposition,[],[f18,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_5
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f46,f53])).

fof(f46,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f68,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f42,f56])).

fof(f42,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f66,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f38,f60])).

fof(f38,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,
    ( spl4_1
    | spl4_2
    | spl4_3
    | spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f24,f48,f44,f40,f36,f32])).

fof(f24,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f17,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n003.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:28:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (3118)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (3118)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (3136)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (3128)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f51,f66,f68,f70,f83,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ~spl4_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    $false | ~spl4_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f34,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f63,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | k1_xboole_0 != sK0),
% 0.21/0.52    inference(forward_demodulation,[],[f62,f30])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | k1_xboole_0 != sK0),
% 0.21/0.52    inference(forward_demodulation,[],[f61,f30])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2),sK3) | k1_xboole_0 != sK0),
% 0.21/0.52    inference(inner_rewriting,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK0),
% 0.21/0.52    inference(definition_unfolding,[],[f13,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f22,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    (k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) & (k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | (k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))) => ((k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) & (k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | (k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)))),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    spl4_1 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ~spl4_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    $false | ~spl4_5),
% 0.21/0.52    inference(subsumption_resolution,[],[f81,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(subsumption_resolution,[],[f59,f30])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | k1_xboole_0 != sK1),
% 0.21/0.52    inference(forward_demodulation,[],[f58,f30])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | k1_xboole_0 != sK1),
% 0.21/0.52    inference(forward_demodulation,[],[f57,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2),sK3) | k1_xboole_0 != sK1),
% 0.21/0.52    inference(inner_rewriting,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK1),
% 0.21/0.52    inference(definition_unfolding,[],[f14,f23])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl4_5),
% 0.21/0.52    inference(subsumption_resolution,[],[f80,f64])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl4_5),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl4_5),
% 0.21/0.52    inference(superposition,[],[f18,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_5),
% 0.21/0.52    inference(subsumption_resolution,[],[f76,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(subsumption_resolution,[],[f55,f30])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | k1_xboole_0 != sK2),
% 0.21/0.52    inference(forward_demodulation,[],[f54,f29])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3) | k1_xboole_0 != sK2),
% 0.21/0.52    inference(inner_rewriting,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK2),
% 0.21/0.52    inference(definition_unfolding,[],[f15,f23])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl4_5),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl4_5),
% 0.21/0.52    inference(superposition,[],[f18,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl4_5),
% 0.21/0.52    inference(subsumption_resolution,[],[f72,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    k1_xboole_0 != sK3),
% 0.21/0.52    inference(subsumption_resolution,[],[f52,f29])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) | k1_xboole_0 != sK3),
% 0.21/0.52    inference(inner_rewriting,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK3),
% 0.21/0.52    inference(definition_unfolding,[],[f16,f23])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3 | ~spl4_5),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3 | ~spl4_5),
% 0.21/0.52    inference(superposition,[],[f18,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl4_5 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ~spl4_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    $false | ~spl4_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f46,f53])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl4_4 <=> k1_xboole_0 = sK3),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~spl4_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    $false | ~spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f42,f56])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    spl4_3 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~spl4_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    $false | ~spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f38,f60])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    spl4_2 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl4_1 | spl4_2 | spl4_3 | spl4_4 | spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f48,f44,f40,f36,f32])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(definition_unfolding,[],[f17,f23])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (3118)------------------------------
% 0.21/0.52  % (3118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3118)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (3118)Memory used [KB]: 10746
% 0.21/0.52  % (3118)Time elapsed: 0.097 s
% 0.21/0.52  % (3118)------------------------------
% 0.21/0.52  % (3118)------------------------------
% 0.21/0.52  % (3109)Success in time 0.159 s
%------------------------------------------------------------------------------
