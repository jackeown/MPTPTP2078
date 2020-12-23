%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:06 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 135 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  157 ( 278 expanded)
%              Number of equality atoms :   37 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1099,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f963,f1059,f1060,f1063,f1098])).

fof(f1098,plain,(
    ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f1096])).

fof(f1096,plain,
    ( $false
    | ~ spl5_14 ),
    inference(resolution,[],[f1027,f30])).

fof(f30,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f1027,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f1025,plain,
    ( spl5_14
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1063,plain,(
    ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f1061])).

fof(f1061,plain,
    ( $false
    | ~ spl5_13 ),
    inference(resolution,[],[f1023,f29])).

fof(f29,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f1023,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f1021,plain,
    ( spl5_13
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1060,plain,
    ( spl5_13
    | spl5_14
    | spl5_9 ),
    inference(avatar_split_clause,[],[f1018,f955,f1025,f1021])).

fof(f955,plain,
    ( spl5_9
  <=> r1_tarski(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1018,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | spl5_9 ),
    inference(resolution,[],[f1017,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f1017,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | spl5_9 ),
    inference(resolution,[],[f1014,f524])).

fof(f524,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f117,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f117,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k4_xboole_0(X5,k4_xboole_0(X5,X4)))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f37,f37])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1014,plain,
    ( ~ r1_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl5_9 ),
    inference(resolution,[],[f957,f351])).

fof(f351,plain,(
    ! [X21,X22] :
      ( r1_tarski(X21,k4_xboole_0(X21,X22))
      | ~ r1_xboole_0(X21,X22) ) ),
    inference(trivial_inequality_removal,[],[f343])).

fof(f343,plain,(
    ! [X21,X22] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X21,k4_xboole_0(X21,X22))
      | ~ r1_xboole_0(X21,X22) ) ),
    inference(superposition,[],[f41,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f957,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f955])).

fof(f1059,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f1056])).

fof(f1056,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f961,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f961,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f959])).

fof(f959,plain,
    ( spl5_10
  <=> r1_tarski(k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f963,plain,
    ( ~ spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f933,f955,f959])).

fof(f933,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),sK2) ),
    inference(extensionality_resolution,[],[f436,f50])).

fof(f50,plain,(
    sK2 != k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f31,f48])).

fof(f31,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f436,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X9,X8)
      | X8 = X9
      | ~ r1_tarski(X8,X9) ) ),
    inference(superposition,[],[f109,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f109,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f51,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (17803)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.46  % (17798)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (17787)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (17798)Refutation not found, incomplete strategy% (17798)------------------------------
% 0.21/0.47  % (17798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17798)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (17798)Memory used [KB]: 10618
% 0.21/0.47  % (17798)Time elapsed: 0.061 s
% 0.21/0.47  % (17798)------------------------------
% 0.21/0.47  % (17798)------------------------------
% 0.21/0.47  % (17801)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (17793)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (17795)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (17788)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (17792)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (17800)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (17790)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (17802)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (17796)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (17791)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (17804)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (17789)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (17799)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (17794)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (17797)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.34/0.53  % (17791)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f1099,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f963,f1059,f1060,f1063,f1098])).
% 1.34/0.53  fof(f1098,plain,(
% 1.34/0.53    ~spl5_14),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f1096])).
% 1.34/0.53  fof(f1096,plain,(
% 1.34/0.53    $false | ~spl5_14),
% 1.34/0.53    inference(resolution,[],[f1027,f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ~r2_hidden(sK1,sK2)),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.34/0.53    inference(ennf_transformation,[],[f15])).
% 1.34/0.53  fof(f15,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.34/0.53    inference(negated_conjecture,[],[f14])).
% 1.34/0.53  fof(f14,conjecture,(
% 1.34/0.53    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.34/0.53  fof(f1027,plain,(
% 1.34/0.53    r2_hidden(sK1,sK2) | ~spl5_14),
% 1.34/0.53    inference(avatar_component_clause,[],[f1025])).
% 1.34/0.53  fof(f1025,plain,(
% 1.34/0.53    spl5_14 <=> r2_hidden(sK1,sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.34/0.53  fof(f1063,plain,(
% 1.34/0.53    ~spl5_13),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f1061])).
% 1.34/0.53  fof(f1061,plain,(
% 1.34/0.53    $false | ~spl5_13),
% 1.34/0.53    inference(resolution,[],[f1023,f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ~r2_hidden(sK0,sK2)),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f1023,plain,(
% 1.34/0.53    r2_hidden(sK0,sK2) | ~spl5_13),
% 1.34/0.53    inference(avatar_component_clause,[],[f1021])).
% 1.34/0.53  fof(f1021,plain,(
% 1.34/0.53    spl5_13 <=> r2_hidden(sK0,sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.34/0.53  fof(f1060,plain,(
% 1.34/0.53    spl5_13 | spl5_14 | spl5_9),
% 1.34/0.53    inference(avatar_split_clause,[],[f1018,f955,f1025,f1021])).
% 1.34/0.53  fof(f955,plain,(
% 1.34/0.53    spl5_9 <=> r1_tarski(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.34/0.53  fof(f1018,plain,(
% 1.34/0.53    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | spl5_9),
% 1.34/0.53    inference(resolution,[],[f1017,f56])).
% 1.34/0.53  fof(f56,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f45,f48])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f35,f47])).
% 1.34/0.53  fof(f47,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f43,f46])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,axiom,(
% 1.34/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.53  fof(f45,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f13])).
% 1.34/0.53  fof(f13,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.34/0.53  fof(f1017,plain,(
% 1.34/0.53    ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | spl5_9),
% 1.34/0.53    inference(resolution,[],[f1014,f524])).
% 1.34/0.53  fof(f524,plain,(
% 1.34/0.53    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 1.34/0.53    inference(resolution,[],[f117,f53])).
% 1.34/0.53  fof(f53,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f38,f37])).
% 1.34/0.53  fof(f37,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,axiom,(
% 1.34/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f16])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.34/0.53    inference(rectify,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.34/0.53  fof(f117,plain,(
% 1.34/0.53    ( ! [X6,X4,X5] : (~r2_hidden(X6,k4_xboole_0(X5,k4_xboole_0(X5,X4))) | ~r1_xboole_0(X4,X5)) )),
% 1.34/0.53    inference(superposition,[],[f52,f51])).
% 1.34/0.53  fof(f51,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f34,f37,f37])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f39,f37])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  fof(f1014,plain,(
% 1.34/0.53    ~r1_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl5_9),
% 1.34/0.53    inference(resolution,[],[f957,f351])).
% 1.34/0.53  fof(f351,plain,(
% 1.34/0.53    ( ! [X21,X22] : (r1_tarski(X21,k4_xboole_0(X21,X22)) | ~r1_xboole_0(X21,X22)) )),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f343])).
% 1.34/0.53  fof(f343,plain,(
% 1.34/0.53    ( ! [X21,X22] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X21,k4_xboole_0(X21,X22)) | ~r1_xboole_0(X21,X22)) )),
% 1.34/0.53    inference(superposition,[],[f41,f69])).
% 1.34/0.53  fof(f69,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.53    inference(resolution,[],[f52,f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.34/0.53    inference(ennf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.34/0.53    inference(nnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.34/0.53  fof(f957,plain,(
% 1.34/0.53    ~r1_tarski(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_9),
% 1.34/0.53    inference(avatar_component_clause,[],[f955])).
% 1.34/0.53  fof(f1059,plain,(
% 1.34/0.53    spl5_10),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f1056])).
% 1.34/0.53  fof(f1056,plain,(
% 1.34/0.53    $false | spl5_10),
% 1.34/0.53    inference(resolution,[],[f961,f33])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.34/0.53  fof(f961,plain,(
% 1.34/0.53    ~r1_tarski(k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),sK2) | spl5_10),
% 1.34/0.53    inference(avatar_component_clause,[],[f959])).
% 1.34/0.53  fof(f959,plain,(
% 1.34/0.53    spl5_10 <=> r1_tarski(k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.34/0.53  fof(f963,plain,(
% 1.34/0.53    ~spl5_10 | ~spl5_9),
% 1.34/0.53    inference(avatar_split_clause,[],[f933,f955,f959])).
% 1.34/0.53  fof(f933,plain,(
% 1.34/0.53    ~r1_tarski(sK2,k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),sK2)),
% 1.34/0.53    inference(extensionality_resolution,[],[f436,f50])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    sK2 != k4_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 1.34/0.53    inference(definition_unfolding,[],[f31,f48])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f436,plain,(
% 1.34/0.53    ( ! [X8,X9] : (~r1_tarski(X9,X8) | X8 = X9 | ~r1_tarski(X8,X9)) )),
% 1.34/0.53    inference(superposition,[],[f109,f54])).
% 1.34/0.53  fof(f54,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f40,f37])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.34/0.53  fof(f109,plain,(
% 1.34/0.53    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 1.34/0.53    inference(superposition,[],[f51,f54])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (17791)------------------------------
% 1.34/0.53  % (17791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (17791)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (17791)Memory used [KB]: 6652
% 1.34/0.53  % (17791)Time elapsed: 0.106 s
% 1.34/0.53  % (17791)------------------------------
% 1.34/0.53  % (17791)------------------------------
% 1.34/0.53  % (17786)Success in time 0.173 s
%------------------------------------------------------------------------------
