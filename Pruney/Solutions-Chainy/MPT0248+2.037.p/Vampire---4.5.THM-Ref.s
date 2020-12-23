%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 140 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  165 ( 461 expanded)
%              Number of equality atoms :  102 ( 372 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f54,f55,f85,f136,f226,f263])).

fof(f263,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl3_1
    | spl3_4
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f260])).

fof(f260,plain,
    ( sK1 != sK1
    | ~ spl3_1
    | spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f140,f225])).

fof(f225,plain,
    ( sK1 = sK2
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl3_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f140,plain,
    ( sK1 != sK2
    | ~ spl3_1
    | spl3_4 ),
    inference(backward_demodulation,[],[f53,f39])).

fof(f39,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f53,plain,
    ( sK2 != k1_tarski(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_4
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f226,plain,
    ( spl3_5
    | spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f220,f38,f42,f223])).

fof(f42,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f220,plain,
    ( k1_xboole_0 = sK2
    | sK1 = sK2
    | ~ spl3_1 ),
    inference(resolution,[],[f215,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | sK1 = X0 )
    | ~ spl3_1 ),
    inference(superposition,[],[f25,f39])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f215,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f112,f139])).

fof(f139,plain,
    ( sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f30,f39])).

fof(f30,plain,(
    k1_tarski(sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(definition_unfolding,[],[f16,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f16,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
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

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f112,plain,(
    ! [X2,X1] : r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f70,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f22,f24,f24])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) ),
    inference(superposition,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f21,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f136,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl3_3
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( sK2 != sK2
    | ~ spl3_3
    | spl3_4 ),
    inference(superposition,[],[f53,f119])).

fof(f119,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f89,f107])).

fof(f107,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f33,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f89,plain,
    ( k1_tarski(sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f30,f48])).

fof(f48,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f84,f47,f38])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f25,f75])).

fof(f75,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f28,f66])).

fof(f66,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f32,f30])).

fof(f55,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f17,f51,f38])).

fof(f17,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f18,f51,f47])).

fof(f18,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f42,f38])).

fof(f19,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:21:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (14285)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (14287)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (14301)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (14285)Refutation not found, incomplete strategy% (14285)------------------------------
% 0.20/0.52  % (14285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14293)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (14285)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (14285)Memory used [KB]: 6140
% 0.20/0.52  % (14285)Time elapsed: 0.106 s
% 0.20/0.52  % (14285)------------------------------
% 0.20/0.52  % (14285)------------------------------
% 0.20/0.53  % (14303)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (14301)Refutation not found, incomplete strategy% (14301)------------------------------
% 0.20/0.53  % (14301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14301)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14301)Memory used [KB]: 10746
% 0.20/0.53  % (14301)Time elapsed: 0.119 s
% 0.20/0.53  % (14301)------------------------------
% 0.20/0.53  % (14301)------------------------------
% 0.20/0.53  % (14289)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (14293)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f45,f54,f55,f85,f136,f226,f263])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    ~spl3_1 | spl3_4 | ~spl3_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f262])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    $false | (~spl3_1 | spl3_4 | ~spl3_5)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f260])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    sK1 != sK1 | (~spl3_1 | spl3_4 | ~spl3_5)),
% 0.20/0.53    inference(superposition,[],[f140,f225])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    sK1 = sK2 | ~spl3_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f223])).
% 0.20/0.53  fof(f223,plain,(
% 0.20/0.53    spl3_5 <=> sK1 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    sK1 != sK2 | (~spl3_1 | spl3_4)),
% 0.20/0.53    inference(backward_demodulation,[],[f53,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    sK1 = k1_tarski(sK0) | ~spl3_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    spl3_1 <=> sK1 = k1_tarski(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    sK2 != k1_tarski(sK0) | spl3_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    spl3_4 <=> sK2 = k1_tarski(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    spl3_5 | spl3_2 | ~spl3_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f220,f38,f42,f223])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    spl3_2 <=> k1_xboole_0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.53  fof(f220,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | sK1 = sK2 | ~spl3_1),
% 0.20/0.53    inference(resolution,[],[f215,f141])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0) ) | ~spl3_1),
% 0.20/0.53    inference(superposition,[],[f25,f39])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.53  fof(f215,plain,(
% 0.20/0.53    r1_tarski(sK2,sK1) | ~spl3_1),
% 0.20/0.53    inference(superposition,[],[f112,f139])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | ~spl3_1),
% 0.20/0.53    inference(backward_demodulation,[],[f30,f39])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    k1_tarski(sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 0.20/0.53    inference(definition_unfolding,[],[f16,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ( ! [X2,X1] : (r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 0.20/0.53    inference(superposition,[],[f70,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f22,f24,f24])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.53    inference(superposition,[],[f28,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f21,f24])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    ~spl3_3 | spl3_4),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    $false | (~spl3_3 | spl3_4)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f128])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    sK2 != sK2 | (~spl3_3 | spl3_4)),
% 0.20/0.53    inference(superposition,[],[f53,f119])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    sK2 = k1_tarski(sK0) | ~spl3_3),
% 0.20/0.53    inference(backward_demodulation,[],[f89,f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.20/0.53    inference(superposition,[],[f33,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f20,f24])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    k1_tarski(sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0)) | ~spl3_3),
% 0.20/0.53    inference(backward_demodulation,[],[f30,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | ~spl3_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    spl3_3 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    spl3_1 | spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f84,f47,f38])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0)),
% 0.20/0.53    inference(resolution,[],[f25,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    r1_tarski(sK1,k1_tarski(sK0))),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,k1_tarski(sK0))),
% 0.20/0.53    inference(superposition,[],[f28,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 0.20/0.53    inference(superposition,[],[f32,f30])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ~spl3_1 | ~spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f17,f51,f38])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ~spl3_3 | ~spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f18,f51,f47])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ~spl3_1 | ~spl3_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f19,f42,f38])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (14293)------------------------------
% 0.20/0.53  % (14293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14293)Termination reason: Refutation
% 0.20/0.53  
% 1.28/0.53  % (14293)Memory used [KB]: 6268
% 1.28/0.53  % (14293)Time elapsed: 0.127 s
% 1.28/0.53  % (14293)------------------------------
% 1.28/0.53  % (14293)------------------------------
% 1.28/0.54  % (14280)Success in time 0.171 s
%------------------------------------------------------------------------------
