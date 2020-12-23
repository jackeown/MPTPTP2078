%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 249 expanded)
%              Number of leaves         :   16 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  187 ( 578 expanded)
%              Number of equality atoms :  121 ( 479 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f63,f70,f158,f159,f160,f162,f174])).

fof(f174,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f172,f167])).

fof(f167,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f49,f57])).

fof(f57,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f49,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_1
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f172,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f171,f52])).

fof(f52,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f171,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f170,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f170,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f169,f114])).

fof(f114,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f106,f21])).

fof(f106,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(superposition,[],[f96,f39])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f24,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f96,plain,(
    ! [X2] : k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) = X2 ),
    inference(forward_demodulation,[],[f92,f21])).

fof(f92,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f40,f21])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f169,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f37,f57])).

fof(f37,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(definition_unfolding,[],[f17,f33,f26])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
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

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f162,plain,
    ( ~ spl3_3
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f161,f67,f51,f56])).

fof(f67,plain,
    ( spl3_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f161,plain,
    ( k1_xboole_0 != sK1
    | ~ spl3_2
    | spl3_5 ),
    inference(backward_demodulation,[],[f69,f52])).

fof(f69,plain,
    ( sK1 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f160,plain,
    ( spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f144,f47,f56])).

fof(f144,plain,
    ( k1_xboole_0 = sK1
    | spl3_1 ),
    inference(subsumption_resolution,[],[f142,f49])).

fof(f142,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f43,f72])).

fof(f72,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f28,f33,f33])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f159,plain,
    ( spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f146,f60,f51])).

fof(f60,plain,
    ( spl3_4
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f146,plain,
    ( k1_xboole_0 = sK2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f143,f62])).

fof(f62,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f143,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f43,f80])).

fof(f80,plain,(
    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f75,f37])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f38,f39])).

fof(f158,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f156,f69])).

fof(f156,plain,
    ( sK1 = sK2
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f61,f48])).

fof(f48,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f61,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f70,plain,
    ( ~ spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f65,f47,f67])).

fof(f65,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f64])).

fof(f64,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f36])).

fof(f36,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f18,f33,f33])).

fof(f18,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f35,f60,f56])).

fof(f35,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f19,f33])).

fof(f19,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f34,f51,f47])).

fof(f34,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f33])).

fof(f20,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:42:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (10159)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (10159)Refutation not found, incomplete strategy% (10159)------------------------------
% 0.22/0.51  % (10159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10167)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (10159)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10159)Memory used [KB]: 6268
% 0.22/0.52  % (10159)Time elapsed: 0.093 s
% 0.22/0.52  % (10159)------------------------------
% 0.22/0.52  % (10159)------------------------------
% 0.22/0.52  % (10182)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (10182)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f54,f63,f70,f158,f159,f160,f162,f174])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f172,f167])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_1 | ~spl3_3)),
% 0.22/0.52    inference(forward_demodulation,[],[f49,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    spl3_3 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    spl3_1 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl3_2 | ~spl3_3)),
% 0.22/0.52    inference(forward_demodulation,[],[f171,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    spl3_2 <=> k1_xboole_0 = sK2),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_3),
% 0.22/0.52    inference(forward_demodulation,[],[f170,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK2,k1_xboole_0) | ~spl3_3),
% 0.22/0.52    inference(forward_demodulation,[],[f169,f114])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.22/0.52    inference(forward_demodulation,[],[f106,f21])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1) )),
% 0.22/0.52    inference(superposition,[],[f96,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f24,f26,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X2] : (k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) = X2) )),
% 0.22/0.52    inference(forward_demodulation,[],[f92,f21])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2))) )),
% 0.22/0.52    inference(superposition,[],[f40,f21])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f27,f26])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0)) | ~spl3_3),
% 0.22/0.52    inference(forward_demodulation,[],[f37,f57])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 0.22/0.52    inference(definition_unfolding,[],[f17,f33,f26])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f22,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f25,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ~spl3_3 | ~spl3_2 | spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f161,f67,f51,f56])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl3_5 <=> sK1 = sK2),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    k1_xboole_0 != sK1 | (~spl3_2 | spl3_5)),
% 0.22/0.52    inference(backward_demodulation,[],[f69,f52])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    sK1 != sK2 | spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f67])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    spl3_3 | spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f144,f47,f56])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | spl3_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f142,f49])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.52    inference(resolution,[],[f43,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.52    inference(superposition,[],[f38,f37])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f23,f26])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.22/0.52    inference(definition_unfolding,[],[f28,f33,f33])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl3_2 | spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f146,f60,f51])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    spl3_4 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | spl3_4),
% 0.22/0.52    inference(subsumption_resolution,[],[f143,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f60])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.52    inference(resolution,[],[f43,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.52    inference(superposition,[],[f75,f37])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 0.22/0.52    inference(superposition,[],[f38,f39])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ~spl3_1 | ~spl3_4 | spl3_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    $false | (~spl3_1 | ~spl3_4 | spl3_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f156,f69])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    sK1 = sK2 | (~spl3_1 | ~spl3_4)),
% 0.22/0.52    inference(forward_demodulation,[],[f61,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ~spl3_5 | ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f65,f47,f67])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 0.22/0.53    inference(inner_rewriting,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 0.22/0.53    inference(inner_rewriting,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.53    inference(definition_unfolding,[],[f18,f33,f33])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ~spl3_3 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f60,f56])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.22/0.53    inference(definition_unfolding,[],[f19,f33])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f51,f47])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    k1_xboole_0 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.53    inference(definition_unfolding,[],[f20,f33])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (10182)------------------------------
% 0.22/0.53  % (10182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10182)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (10182)Memory used [KB]: 6268
% 0.22/0.53  % (10182)Time elapsed: 0.107 s
% 0.22/0.53  % (10182)------------------------------
% 0.22/0.53  % (10182)------------------------------
% 0.22/0.53  % (10154)Success in time 0.164 s
%------------------------------------------------------------------------------
