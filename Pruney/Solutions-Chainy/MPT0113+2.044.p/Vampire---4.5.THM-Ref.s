%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 168 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  142 ( 294 expanded)
%              Number of equality atoms :   43 ( 114 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f66,f103,f188,f228,f290,f376])).

fof(f376,plain,
    ( spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f374,f61])).

fof(f61,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f374,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f366,f69])).

fof(f69,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f366,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f142,f289])).

fof(f289,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f142,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4) ),
    inference(superposition,[],[f31,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f290,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f253,f225,f287])).

fof(f225,plain,
    ( spl3_5
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f253,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f242,f139])).

fof(f139,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f135,f69])).

fof(f135,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f45,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f46,f69])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f242,plain,
    ( k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0)
    | ~ spl3_5 ),
    inference(superposition,[],[f45,f227])).

fof(f227,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f225])).

fof(f228,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f223,f185,f54,f225])).

fof(f54,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f185,plain,
    ( spl3_4
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f223,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f97,f222])).

fof(f222,plain,
    ( ! [X1] : k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k4_xboole_0(X1,sK2))
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f200,f221])).

fof(f221,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) ),
    inference(forward_demodulation,[],[f220,f69])).

fof(f220,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) ),
    inference(forward_demodulation,[],[f210,f74])).

fof(f210,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X9)) ),
    inference(superposition,[],[f52,f69])).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f43,f34])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f200,plain,
    ( ! [X1] : k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X1),k1_xboole_0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f197,f74])).

fof(f197,plain,
    ( ! [X1] : k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X1),k4_xboole_0(sK0,sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f52,f187])).

fof(f187,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f185])).

fof(f97,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f56,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f56,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f188,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f106,f63,f185])).

fof(f63,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f106,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f64,f40])).

fof(f64,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f103,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f82,f54,f63])).

fof(f82,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f32,f56,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f66,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f27,f63,f59])).

fof(f27,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.47  % (8308)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (8307)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (8321)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (8312)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (8310)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (8320)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (8311)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (8309)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (8323)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (8319)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (8317)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (8315)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (8313)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (8316)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (8314)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (8322)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (8324)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (8318)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (8322)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 1.19/0.53  % SZS output start Proof for theBenchmark
% 1.19/0.53  fof(f377,plain,(
% 1.19/0.53    $false),
% 1.19/0.53    inference(avatar_sat_refutation,[],[f57,f66,f103,f188,f228,f290,f376])).
% 1.19/0.53  fof(f376,plain,(
% 1.19/0.53    spl3_2 | ~spl3_6),
% 1.19/0.53    inference(avatar_contradiction_clause,[],[f375])).
% 1.19/0.53  fof(f375,plain,(
% 1.19/0.53    $false | (spl3_2 | ~spl3_6)),
% 1.19/0.53    inference(subsumption_resolution,[],[f374,f61])).
% 1.19/0.53  fof(f61,plain,(
% 1.19/0.53    ~r1_tarski(sK0,sK1) | spl3_2),
% 1.19/0.53    inference(avatar_component_clause,[],[f59])).
% 1.19/0.53  fof(f59,plain,(
% 1.19/0.53    spl3_2 <=> r1_tarski(sK0,sK1)),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.19/0.53  fof(f374,plain,(
% 1.19/0.53    r1_tarski(sK0,sK1) | ~spl3_6),
% 1.19/0.53    inference(forward_demodulation,[],[f366,f69])).
% 1.19/0.53  fof(f69,plain,(
% 1.19/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f28,f40])).
% 1.19/0.53  fof(f40,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.19/0.53    inference(cnf_transformation,[],[f25])).
% 1.19/0.53  fof(f25,plain,(
% 1.19/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.19/0.53    inference(nnf_transformation,[],[f13])).
% 1.19/0.53  fof(f13,axiom,(
% 1.19/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.19/0.53  fof(f28,plain,(
% 1.19/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f11])).
% 1.19/0.53  fof(f11,axiom,(
% 1.19/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.19/0.53  fof(f366,plain,(
% 1.19/0.53    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1) | ~spl3_6),
% 1.19/0.53    inference(superposition,[],[f142,f289])).
% 1.19/0.53  fof(f289,plain,(
% 1.19/0.53    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_6),
% 1.19/0.53    inference(avatar_component_clause,[],[f287])).
% 1.19/0.53  fof(f287,plain,(
% 1.19/0.53    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.19/0.53  fof(f142,plain,(
% 1.19/0.53    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) )),
% 1.19/0.53    inference(superposition,[],[f31,f47])).
% 1.19/0.53  fof(f47,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.19/0.53    inference(definition_unfolding,[],[f33,f34,f34])).
% 1.19/0.53  fof(f34,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f7])).
% 1.19/0.53  fof(f7,axiom,(
% 1.19/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.19/0.53  fof(f33,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f1])).
% 1.19/0.53  fof(f1,axiom,(
% 1.19/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.19/0.53  fof(f31,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f6])).
% 1.19/0.53  fof(f6,axiom,(
% 1.19/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.19/0.53  fof(f290,plain,(
% 1.19/0.53    spl3_6 | ~spl3_5),
% 1.19/0.53    inference(avatar_split_clause,[],[f253,f225,f287])).
% 1.19/0.53  fof(f225,plain,(
% 1.19/0.53    spl3_5 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.19/0.53  fof(f253,plain,(
% 1.19/0.53    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_5),
% 1.19/0.53    inference(forward_demodulation,[],[f242,f139])).
% 1.19/0.53  fof(f139,plain,(
% 1.19/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.19/0.53    inference(forward_demodulation,[],[f135,f69])).
% 1.19/0.53  fof(f135,plain,(
% 1.19/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.19/0.53    inference(superposition,[],[f45,f74])).
% 1.19/0.53  fof(f74,plain,(
% 1.19/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.19/0.53    inference(backward_demodulation,[],[f46,f69])).
% 1.19/0.53  fof(f46,plain,(
% 1.19/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.19/0.53    inference(definition_unfolding,[],[f29,f34])).
% 1.19/0.53  fof(f29,plain,(
% 1.19/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f5])).
% 1.19/0.53  fof(f5,axiom,(
% 1.19/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.19/0.53  fof(f45,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.19/0.53    inference(definition_unfolding,[],[f35,f34])).
% 1.19/0.53  fof(f35,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f3])).
% 1.19/0.53  fof(f3,axiom,(
% 1.19/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.19/0.53  fof(f242,plain,(
% 1.19/0.53    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0) | ~spl3_5),
% 1.19/0.53    inference(superposition,[],[f45,f227])).
% 1.19/0.53  fof(f227,plain,(
% 1.19/0.53    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.19/0.53    inference(avatar_component_clause,[],[f225])).
% 1.19/0.53  fof(f228,plain,(
% 1.19/0.53    spl3_5 | ~spl3_1 | ~spl3_4),
% 1.19/0.53    inference(avatar_split_clause,[],[f223,f185,f54,f225])).
% 1.19/0.53  fof(f54,plain,(
% 1.19/0.53    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.19/0.53  fof(f185,plain,(
% 1.19/0.53    spl3_4 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.19/0.53  fof(f223,plain,(
% 1.19/0.53    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_4)),
% 1.19/0.53    inference(backward_demodulation,[],[f97,f222])).
% 1.19/0.53  fof(f222,plain,(
% 1.19/0.53    ( ! [X1] : (k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k4_xboole_0(X1,sK2))) ) | ~spl3_4),
% 1.19/0.53    inference(backward_demodulation,[],[f200,f221])).
% 1.19/0.53  fof(f221,plain,(
% 1.19/0.53    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0)) )),
% 1.19/0.53    inference(forward_demodulation,[],[f220,f69])).
% 1.19/0.53  fof(f220,plain,(
% 1.19/0.53    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0)) )),
% 1.19/0.53    inference(forward_demodulation,[],[f210,f74])).
% 1.19/0.53  fof(f210,plain,(
% 1.19/0.53    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X9))) )),
% 1.19/0.53    inference(superposition,[],[f52,f69])).
% 1.19/0.53  fof(f52,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.19/0.53    inference(definition_unfolding,[],[f43,f34])).
% 1.19/0.53  fof(f43,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f8])).
% 1.19/0.53  fof(f8,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.19/0.53  fof(f200,plain,(
% 1.19/0.53    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X1),k1_xboole_0)) ) | ~spl3_4),
% 1.19/0.53    inference(forward_demodulation,[],[f197,f74])).
% 1.19/0.53  fof(f197,plain,(
% 1.19/0.53    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X1),k4_xboole_0(sK0,sK0))) ) | ~spl3_4),
% 1.19/0.53    inference(superposition,[],[f52,f187])).
% 1.19/0.53  fof(f187,plain,(
% 1.19/0.53    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_4),
% 1.19/0.53    inference(avatar_component_clause,[],[f185])).
% 1.19/0.53  fof(f97,plain,(
% 1.19/0.53    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_1),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f56,f49])).
% 1.19/0.53  fof(f49,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.19/0.53    inference(definition_unfolding,[],[f37,f34])).
% 1.19/0.53  fof(f37,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f19])).
% 1.19/0.53  fof(f19,plain,(
% 1.19/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.19/0.53    inference(ennf_transformation,[],[f4])).
% 1.19/0.53  fof(f4,axiom,(
% 1.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.19/0.53  fof(f56,plain,(
% 1.19/0.53    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 1.19/0.53    inference(avatar_component_clause,[],[f54])).
% 1.19/0.53  fof(f188,plain,(
% 1.19/0.53    spl3_4 | ~spl3_3),
% 1.19/0.53    inference(avatar_split_clause,[],[f106,f63,f185])).
% 1.19/0.53  fof(f63,plain,(
% 1.19/0.53    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.19/0.53  fof(f106,plain,(
% 1.19/0.53    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f64,f40])).
% 1.19/0.53  fof(f64,plain,(
% 1.19/0.53    r1_xboole_0(sK0,sK2) | ~spl3_3),
% 1.19/0.53    inference(avatar_component_clause,[],[f63])).
% 1.19/0.53  fof(f103,plain,(
% 1.19/0.53    spl3_3 | ~spl3_1),
% 1.19/0.53    inference(avatar_split_clause,[],[f82,f54,f63])).
% 1.19/0.53  fof(f82,plain,(
% 1.19/0.53    r1_xboole_0(sK0,sK2) | ~spl3_1),
% 1.19/0.53    inference(unit_resulting_resolution,[],[f32,f56,f44])).
% 1.19/0.53  fof(f44,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f21])).
% 1.19/0.53  fof(f21,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.19/0.53    inference(flattening,[],[f20])).
% 1.19/0.53  fof(f20,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.19/0.53    inference(ennf_transformation,[],[f10])).
% 1.19/0.53  fof(f10,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.19/0.53  fof(f32,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f12])).
% 1.19/0.53  fof(f12,axiom,(
% 1.19/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.19/0.53  fof(f66,plain,(
% 1.19/0.53    ~spl3_2 | ~spl3_3),
% 1.19/0.53    inference(avatar_split_clause,[],[f27,f63,f59])).
% 1.19/0.53  fof(f27,plain,(
% 1.19/0.53    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.19/0.53    inference(cnf_transformation,[],[f23])).
% 1.19/0.53  fof(f23,plain,(
% 1.19/0.53    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).
% 1.19/0.53  fof(f22,plain,(
% 1.19/0.53    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f18,plain,(
% 1.19/0.53    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.19/0.53    inference(ennf_transformation,[],[f17])).
% 1.19/0.53  fof(f17,negated_conjecture,(
% 1.19/0.53    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.19/0.53    inference(negated_conjecture,[],[f16])).
% 1.19/0.53  fof(f16,conjecture,(
% 1.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.19/0.53  fof(f57,plain,(
% 1.19/0.53    spl3_1),
% 1.19/0.53    inference(avatar_split_clause,[],[f26,f54])).
% 1.19/0.53  fof(f26,plain,(
% 1.19/0.53    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.19/0.53    inference(cnf_transformation,[],[f23])).
% 1.19/0.53  % SZS output end Proof for theBenchmark
% 1.19/0.53  % (8322)------------------------------
% 1.19/0.53  % (8322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (8322)Termination reason: Refutation
% 1.19/0.53  
% 1.19/0.53  % (8322)Memory used [KB]: 10874
% 1.19/0.53  % (8322)Time elapsed: 0.096 s
% 1.19/0.53  % (8322)------------------------------
% 1.19/0.53  % (8322)------------------------------
% 1.19/0.53  % (8306)Success in time 0.156 s
%------------------------------------------------------------------------------
