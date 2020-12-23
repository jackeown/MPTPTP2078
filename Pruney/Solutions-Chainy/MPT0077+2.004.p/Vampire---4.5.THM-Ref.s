%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 131 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  169 ( 351 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (28923)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f1007,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f55,f389,f474,f1005])).

% (28930)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f1005,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f1004])).

fof(f1004,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f476,f989])).

fof(f989,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f478,f768])).

fof(f768,plain,
    ( ! [X0] : k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f754,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f754,plain,
    ( ! [X0] : k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
    | ~ spl3_3 ),
    inference(superposition,[],[f33,f679])).

fof(f679,plain,
    ( ! [X14] : k4_xboole_0(sK0,k2_xboole_0(sK1,X14)) = k4_xboole_0(sK0,X14)
    | ~ spl3_3 ),
    inference(superposition,[],[f39,f493])).

fof(f493,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f400,f59])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f32,f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f400,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(superposition,[],[f35,f394])).

fof(f394,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f53,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f53,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f478,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f476,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f44,f37])).

fof(f44,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f474,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f81,f465])).

fof(f465,plain,
    ( ! [X2] : k1_xboole_0 != k3_xboole_0(k2_xboole_0(X2,sK2),sK0)
    | spl3_1 ),
    inference(resolution,[],[f452,f38])).

fof(f452,plain,
    ( ! [X1] : ~ r1_xboole_0(k2_xboole_0(X1,sK2),sK0)
    | spl3_1 ),
    inference(resolution,[],[f395,f62])).

fof(f62,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f30,f32])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f395,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_xboole_0(X0,sK0) )
    | spl3_1 ),
    inference(resolution,[],[f392,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f392,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl3_1 ),
    inference(resolution,[],[f43,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f43,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f81,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f37,f36])).

fof(f389,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f81,f379])).

fof(f379,plain,
    ( ! [X2] : k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK1,X2),sK0)
    | spl3_3 ),
    inference(resolution,[],[f375,f38])).

fof(f375,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(sK1,X0),sK0)
    | spl3_3 ),
    inference(resolution,[],[f331,f30])).

fof(f331,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | ~ r1_xboole_0(X1,sK0) )
    | spl3_3 ),
    inference(resolution,[],[f40,f57])).

fof(f57,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl3_3 ),
    inference(resolution,[],[f36,f52])).

fof(f52,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f55,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f42,f51,f46])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f54,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f26,f46,f51])).

fof(f26,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f27,f46,f42])).

fof(f27,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:24:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.47  % (28924)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (28927)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (28938)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (28925)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (28935)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (28922)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (28926)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (28936)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (28939)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (28928)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (28931)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (28933)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (28938)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  % (28923)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  fof(f1007,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f49,f54,f55,f389,f474,f1005])).
% 0.22/0.51  % (28930)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  fof(f1005,plain,(
% 0.22/0.51    ~spl3_1 | spl3_2 | ~spl3_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f1004])).
% 0.22/0.51  fof(f1004,plain,(
% 0.22/0.51    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f476,f989])).
% 0.22/0.51  fof(f989,plain,(
% 0.22/0.51    k1_xboole_0 != k3_xboole_0(sK0,sK2) | (spl3_2 | ~spl3_3)),
% 0.22/0.51    inference(superposition,[],[f478,f768])).
% 0.22/0.51  fof(f768,plain,(
% 0.22/0.51    ( ! [X0] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) ) | ~spl3_3),
% 0.22/0.51    inference(forward_demodulation,[],[f754,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.51  fof(f754,plain,(
% 0.22/0.51    ( ! [X0] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f33,f679])).
% 0.22/0.51  fof(f679,plain,(
% 0.22/0.51    ( ! [X14] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X14)) = k4_xboole_0(sK0,X14)) ) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f39,f493])).
% 0.22/0.51  fof(f493,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f400,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.51    inference(superposition,[],[f32,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.51  fof(f400,plain,(
% 0.22/0.51    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f35,f394])).
% 0.22/0.51  fof(f394,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f53,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    r1_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.51  fof(f478,plain,(
% 0.22/0.51    k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.22/0.51    inference(resolution,[],[f47,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    spl3_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f476,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_1),
% 0.22/0.51    inference(resolution,[],[f44,f37])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    r1_xboole_0(sK0,sK2) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f474,plain,(
% 0.22/0.51    spl3_1 | ~spl3_2),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f473])).
% 0.22/0.51  fof(f473,plain,(
% 0.22/0.51    $false | (spl3_1 | ~spl3_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f81,f465])).
% 0.22/0.51  fof(f465,plain,(
% 0.22/0.51    ( ! [X2] : (k1_xboole_0 != k3_xboole_0(k2_xboole_0(X2,sK2),sK0)) ) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f452,f38])).
% 0.22/0.51  fof(f452,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_xboole_0(k2_xboole_0(X1,sK2),sK0)) ) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f395,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.22/0.51    inference(superposition,[],[f30,f32])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.51  fof(f395,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_xboole_0(X0,sK0)) ) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f392,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.51  fof(f392,plain,(
% 0.22/0.51    ~r1_xboole_0(sK2,sK0) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f43,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f42])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f75,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f46])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.51    inference(resolution,[],[f37,f36])).
% 0.22/0.51  fof(f389,plain,(
% 0.22/0.51    ~spl3_2 | spl3_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f388])).
% 0.22/0.51  fof(f388,plain,(
% 0.22/0.51    $false | (~spl3_2 | spl3_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f81,f379])).
% 0.22/0.51  fof(f379,plain,(
% 0.22/0.51    ( ! [X2] : (k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK1,X2),sK0)) ) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f375,f38])).
% 0.22/0.51  fof(f375,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(sK1,X0),sK0)) ) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f331,f30])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_tarski(sK1,X1) | ~r1_xboole_0(X1,sK0)) ) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f40,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ~r1_xboole_0(sK1,sK0) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f36,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK1) | spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f51])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ~spl3_2 | ~spl3_3 | ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f22,f42,f51,f46])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.51    inference(negated_conjecture,[],[f13])).
% 0.22/0.51  fof(f13,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    spl3_3 | spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f46,f51])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    spl3_1 | spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f46,f42])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28938)------------------------------
% 0.22/0.51  % (28938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28938)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28938)Memory used [KB]: 6524
% 0.22/0.51  % (28938)Time elapsed: 0.032 s
% 0.22/0.51  % (28938)------------------------------
% 0.22/0.51  % (28938)------------------------------
% 0.22/0.51  % (28929)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (28933)Refutation not found, incomplete strategy% (28933)------------------------------
% 0.22/0.51  % (28933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28933)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28933)Memory used [KB]: 10746
% 0.22/0.51  % (28933)Time elapsed: 0.096 s
% 0.22/0.51  % (28933)------------------------------
% 0.22/0.51  % (28933)------------------------------
% 0.22/0.52  % (28921)Success in time 0.146 s
%------------------------------------------------------------------------------
