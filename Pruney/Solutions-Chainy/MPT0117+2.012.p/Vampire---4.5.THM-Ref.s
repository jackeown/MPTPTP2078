%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 120 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   19
%              Number of atoms          :  113 ( 199 expanded)
%              Number of equality atoms :   39 (  68 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f659,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f620,f648,f658])).

fof(f658,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f653,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f653,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK0)
    | spl3_5 ),
    inference(superposition,[],[f649,f488])).

fof(f488,plain,(
    sK0 = k3_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f487,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f487,plain,(
    k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f479,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f479,plain,(
    k3_xboole_0(sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f203,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f203,plain,(
    k3_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f189,f28])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f189,plain,(
    k3_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f31,f63])).

fof(f63,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f61,f26])).

fof(f61,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f29,f59])).

fof(f59,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f55,f25])).

fof(f55,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f30,f44])).

fof(f44,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f649,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))
    | spl3_5 ),
    inference(resolution,[],[f615,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f615,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f613])).

fof(f613,plain,
    ( spl3_5
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f648,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f645,f27])).

fof(f645,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK0),sK2)
    | spl3_6 ),
    inference(superposition,[],[f633,f320])).

fof(f320,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f319,f257])).

fof(f257,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f233,f36])).

fof(f36,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f28,f26])).

fof(f233,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f25])).

fof(f319,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f311,f28])).

fof(f311,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f190,f33])).

fof(f190,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(superposition,[],[f31,f67])).

fof(f67,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f65,f26])).

fof(f65,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f29,f60])).

fof(f60,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f56,f25])).

fof(f56,plain,(
    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f30,f45])).

fof(f45,plain,(
    sK2 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f633,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK2,sK0),k3_xboole_0(sK1,X0))
    | spl3_6 ),
    inference(resolution,[],[f619,f34])).

fof(f619,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK0),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f617])).

fof(f617,plain,
    ( spl3_6
  <=> r1_tarski(k4_xboole_0(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f620,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f572,f617,f613])).

fof(f572,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK0),sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:29:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (32287)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (32298)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (32288)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (32293)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (32289)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (32297)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (32286)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (32295)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (32290)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (32299)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (32291)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (32285)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (32296)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (32294)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (32302)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (32301)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (32300)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (32292)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.54  % (32301)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f659,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f620,f648,f658])).
% 0.22/0.54  fof(f658,plain,(
% 0.22/0.54    spl3_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f656])).
% 0.22/0.54  fof(f656,plain,(
% 0.22/0.54    $false | spl3_5),
% 0.22/0.54    inference(resolution,[],[f653,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.54  fof(f653,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK0,sK2),sK0) | spl3_5),
% 0.22/0.54    inference(superposition,[],[f649,f488])).
% 0.22/0.54  fof(f488,plain,(
% 0.22/0.54    sK0 = k3_xboole_0(sK1,sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f487,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.54  fof(f487,plain,(
% 0.22/0.54    k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK1,sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f479,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.54  fof(f479,plain,(
% 0.22/0.54    k3_xboole_0(sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 0.22/0.54    inference(superposition,[],[f203,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    k3_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f189,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    k3_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1)),
% 0.22/0.54    inference(superposition,[],[f31,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    sK1 = k2_xboole_0(sK1,sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f61,f26])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.22/0.54    inference(superposition,[],[f29,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f55,f25])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0)),
% 0.22/0.54    inference(superposition,[],[f30,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.54    inference(resolution,[],[f32,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.22/0.54  fof(f649,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) ) | spl3_5),
% 0.22/0.54    inference(resolution,[],[f615,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.22/0.54  fof(f615,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) | spl3_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f613])).
% 0.22/0.54  fof(f613,plain,(
% 0.22/0.54    spl3_5 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f648,plain,(
% 0.22/0.54    spl3_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f646])).
% 0.22/0.54  fof(f646,plain,(
% 0.22/0.54    $false | spl3_6),
% 0.22/0.54    inference(resolution,[],[f645,f27])).
% 0.22/0.54  fof(f645,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK2,sK0),sK2) | spl3_6),
% 0.22/0.54    inference(superposition,[],[f633,f320])).
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    sK2 = k3_xboole_0(sK1,sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f319,f257])).
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.22/0.54    inference(forward_demodulation,[],[f233,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.22/0.54    inference(superposition,[],[f28,f26])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(superposition,[],[f33,f25])).
% 0.22/0.54  fof(f319,plain,(
% 0.22/0.54    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 0.22/0.54    inference(forward_demodulation,[],[f311,f28])).
% 0.22/0.54  fof(f311,plain,(
% 0.22/0.54    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),
% 0.22/0.54    inference(superposition,[],[f190,f33])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 0.22/0.54    inference(superposition,[],[f31,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    sK1 = k2_xboole_0(sK1,sK2)),
% 0.22/0.54    inference(forward_demodulation,[],[f65,f26])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.54    inference(superposition,[],[f29,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f56,f25])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2)),
% 0.22/0.54    inference(superposition,[],[f30,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    sK2 = k3_xboole_0(sK2,sK1)),
% 0.22/0.54    inference(resolution,[],[f32,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    r1_tarski(sK2,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f633,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK2,sK0),k3_xboole_0(sK1,X0))) ) | spl3_6),
% 0.22/0.54    inference(resolution,[],[f619,f34])).
% 0.22/0.54  fof(f619,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK2,sK0),sK1) | spl3_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f617])).
% 0.22/0.54  fof(f617,plain,(
% 0.22/0.54    spl3_6 <=> r1_tarski(k4_xboole_0(sK2,sK0),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.54  fof(f620,plain,(
% 0.22/0.54    ~spl3_5 | ~spl3_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f572,f617,f613])).
% 0.22/0.54  fof(f572,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK2,sK0),sK1) | ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.54    inference(resolution,[],[f35,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X1),X2) | ~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X1),X2) | ~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X1),X2) | (~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (32301)------------------------------
% 0.22/0.54  % (32301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32301)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (32301)Memory used [KB]: 6524
% 0.22/0.54  % (32301)Time elapsed: 0.110 s
% 0.22/0.54  % (32301)------------------------------
% 0.22/0.54  % (32301)------------------------------
% 0.22/0.54  % (32283)Success in time 0.174 s
%------------------------------------------------------------------------------
