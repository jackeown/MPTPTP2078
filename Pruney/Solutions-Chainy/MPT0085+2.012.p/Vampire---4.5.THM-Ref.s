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
% DateTime   : Thu Dec  3 12:31:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 124 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  174 ( 252 expanded)
%              Number of equality atoms :   52 (  88 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f87,f92,f104,f109,f129,f133,f253,f291,f313,f319])).

fof(f319,plain,
    ( spl5_12
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl5_12
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(trivial_inequality_removal,[],[f317])).

fof(f317,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl5_12
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(backward_demodulation,[],[f103,f315])).

fof(f315,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(superposition,[],[f128,f312])).

fof(f312,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl5_30
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f128,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_16
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f103,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_12
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f313,plain,
    ( spl5_30
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f297,f288,f251,f310])).

fof(f251,plain,
    ( spl5_24
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f288,plain,
    ( spl5_28
  <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f297,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(superposition,[],[f290,f252])).

fof(f252,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f251])).

fof(f290,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f288])).

fof(f291,plain,
    ( spl5_28
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f218,f131,f106,f288])).

fof(f106,plain,
    ( spl5_13
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f131,plain,
    ( spl5_17
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f218,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(superposition,[],[f132,f108])).

fof(f108,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f132,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f131])).

fof(f253,plain,
    ( spl5_24
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f237,f131,f50,f46,f251])).

fof(f46,plain,
    ( spl5_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f50,plain,
    ( spl5_3
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f237,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f219,f51])).

fof(f51,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f219,plain,
    ( ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(superposition,[],[f132,f47])).

fof(f47,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f133,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f36,f131])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f129,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f33,f127])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f109,plain,
    ( spl5_13
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f93,f90,f54,f106])).

fof(f54,plain,
    ( spl5_4
  <=> ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f90,plain,
    ( spl5_10
  <=> ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f93,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(resolution,[],[f91,f55])).

fof(f55,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f91,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f104,plain,(
    ~ spl5_12 ),
    inference(avatar_split_clause,[],[f34,f101])).

fof(f34,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f23,f29,f29])).

fof(f23,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f92,plain,
    ( spl5_10
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f88,f85,f41,f90])).

fof(f41,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f85,plain,
    ( spl5_9
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f88,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(resolution,[],[f86,f43])).

fof(f43,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f56,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f52,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f39,f50])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f35,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f48,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f44,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:52:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (22172)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (22168)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (22180)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (22167)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (22170)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (22172)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f320,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f87,f92,f104,f109,f129,f133,f253,f291,f313,f319])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    spl5_12 | ~spl5_16 | ~spl5_30),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f318])).
% 0.21/0.47  fof(f318,plain,(
% 0.21/0.47    $false | (spl5_12 | ~spl5_16 | ~spl5_30)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f317])).
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (spl5_12 | ~spl5_16 | ~spl5_30)),
% 0.21/0.47    inference(backward_demodulation,[],[f103,f315])).
% 0.21/0.47  fof(f315,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | (~spl5_16 | ~spl5_30)),
% 0.21/0.47    inference(superposition,[],[f128,f312])).
% 0.21/0.47  fof(f312,plain,(
% 0.21/0.47    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_30),
% 0.21/0.47    inference(avatar_component_clause,[],[f310])).
% 0.21/0.47  fof(f310,plain,(
% 0.21/0.47    spl5_30 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl5_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl5_16 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl5_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl5_12 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.47  fof(f313,plain,(
% 0.21/0.47    spl5_30 | ~spl5_24 | ~spl5_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f297,f288,f251,f310])).
% 0.21/0.47  fof(f251,plain,(
% 0.21/0.47    spl5_24 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.47  fof(f288,plain,(
% 0.21/0.47    spl5_28 <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.47  fof(f297,plain,(
% 0.21/0.47    sK0 = k4_xboole_0(sK0,sK1) | (~spl5_24 | ~spl5_28)),
% 0.21/0.47    inference(superposition,[],[f290,f252])).
% 0.21/0.47  fof(f252,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl5_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f251])).
% 0.21/0.47  fof(f290,plain,(
% 0.21/0.47    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl5_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f288])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    spl5_28 | ~spl5_13 | ~spl5_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f218,f131,f106,f288])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl5_13 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    spl5_17 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.47  fof(f218,plain,(
% 0.21/0.47    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | (~spl5_13 | ~spl5_17)),
% 0.21/0.47    inference(superposition,[],[f132,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f106])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl5_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f131])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    spl5_24 | ~spl5_2 | ~spl5_3 | ~spl5_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f237,f131,f50,f46,f251])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl5_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl5_3 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl5_2 | ~spl5_3 | ~spl5_17)),
% 0.21/0.47    inference(forward_demodulation,[],[f219,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0) ) | (~spl5_2 | ~spl5_17)),
% 0.21/0.47    inference(superposition,[],[f132,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl5_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f131])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f30,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl5_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f127])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl5_13 | ~spl5_4 | ~spl5_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f93,f90,f54,f106])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl5_4 <=> ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl5_10 <=> ! [X0] : ~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl5_4 | ~spl5_10)),
% 0.21/0.47    inference(resolution,[],[f91,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl5_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f90])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ~spl5_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f101])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.47    inference(definition_unfolding,[],[f23,f29,f29])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl5_10 | ~spl5_1 | ~spl5_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f88,f85,f41,f90])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl5_9 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | (~spl5_1 | ~spl5_9)),
% 0.21/0.47    inference(resolution,[],[f86,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl5_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl5_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f85])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f32,f29])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f50])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f35,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f24,f29])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f46])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f41])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    r1_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (22172)------------------------------
% 0.21/0.47  % (22172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22172)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (22172)Memory used [KB]: 6268
% 0.21/0.47  % (22172)Time elapsed: 0.058 s
% 0.21/0.47  % (22172)------------------------------
% 0.21/0.47  % (22172)------------------------------
% 0.21/0.47  % (22164)Success in time 0.111 s
%------------------------------------------------------------------------------
