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
% DateTime   : Thu Dec  3 12:40:49 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 193 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  114 ( 264 expanded)
%              Number of equality atoms :   71 ( 202 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f72,f77,f592])).

fof(f592,plain,
    ( spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f579,f74,f54])).

fof(f54,plain,
    ( spl2_2
  <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f74,plain,
    ( spl2_5
  <=> k1_xboole_0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f579,plain,
    ( sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f562,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f562,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_5 ),
    inference(superposition,[],[f335,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f335,plain,
    ( ! [X0] : k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = X0
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f78,f323])).

fof(f323,plain,
    ( ! [X8] : k5_xboole_0(k1_xboole_0,X8) = X8
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f311,f23])).

fof(f311,plain,
    ( ! [X8] : k5_xboole_0(X8,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X8,k1_xboole_0))
    | ~ spl2_5 ),
    inference(superposition,[],[f266,f25])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f266,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_5 ),
    inference(superposition,[],[f250,f78])).

fof(f250,plain,
    ( ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0))
    | ~ spl2_5 ),
    inference(superposition,[],[f225,f25])).

fof(f225,plain,
    ( ! [X9] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,sK0)) = k5_xboole_0(sK0,X9)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f207,f23])).

fof(f207,plain,
    ( ! [X9] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,sK0)) = k5_xboole_0(sK0,k5_xboole_0(X9,k1_xboole_0))
    | ~ spl2_5 ),
    inference(superposition,[],[f99,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f99,plain,
    ( ! [X2,X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(sK0,k5_xboole_0(X2,k5_xboole_0(X3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl2_5 ),
    inference(superposition,[],[f80,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f80,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_5 ),
    inference(superposition,[],[f78,f25])).

fof(f78,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))
    | ~ spl2_5 ),
    inference(superposition,[],[f32,f76])).

fof(f77,plain,
    ( ~ spl2_4
    | spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f63,f59,f74,f69])).

fof(f69,plain,
    ( spl2_4
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( spl2_3
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f63,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ spl2_3 ),
    inference(superposition,[],[f61,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f42,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f61,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f72,plain,
    ( spl2_4
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f64,f59,f49,f69])).

fof(f49,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f64,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0)
    | ~ spl2_3 ),
    inference(superposition,[],[f61,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f29,f27,f42])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f62,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f44,f59])).

fof(f44,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f19,f27,f42])).

fof(f19,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f57,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f43,f54])).

fof(f43,plain,(
    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f21,f42])).

fof(f21,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f17])).

% (17886)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f52,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:38:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.54  % (17873)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (17881)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (17889)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (17871)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (17870)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (17883)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (17880)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.57/0.58  % (17869)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.57/0.58  % (17867)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.57/0.58  % (17875)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.57/0.58  % (17868)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.57/0.58  % (17867)Refutation not found, incomplete strategy% (17867)------------------------------
% 1.57/0.58  % (17867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (17867)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (17867)Memory used [KB]: 1663
% 1.57/0.58  % (17867)Time elapsed: 0.117 s
% 1.57/0.58  % (17867)------------------------------
% 1.57/0.58  % (17867)------------------------------
% 1.57/0.59  % (17872)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.57/0.59  % (17885)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.59  % (17891)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.60  % (17889)Refutation found. Thanks to Tanya!
% 1.57/0.60  % SZS status Theorem for theBenchmark
% 1.82/0.60  % (17890)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.82/0.60  % (17884)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.82/0.60  % (17895)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.82/0.60  % (17882)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.82/0.60  % (17882)Refutation not found, incomplete strategy% (17882)------------------------------
% 1.82/0.60  % (17882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.60  % (17882)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.60  
% 1.82/0.60  % (17882)Memory used [KB]: 6140
% 1.82/0.60  % (17882)Time elapsed: 0.002 s
% 1.82/0.60  % (17882)------------------------------
% 1.82/0.60  % (17882)------------------------------
% 1.82/0.60  % (17894)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.82/0.60  % (17876)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.82/0.60  % (17877)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.82/0.60  % (17887)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.82/0.61  % (17877)Refutation not found, incomplete strategy% (17877)------------------------------
% 1.82/0.61  % (17877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (17877)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.61  
% 1.82/0.61  % (17877)Memory used [KB]: 10618
% 1.82/0.61  % (17877)Time elapsed: 0.182 s
% 1.82/0.61  % (17874)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.82/0.61  % (17877)------------------------------
% 1.82/0.61  % (17877)------------------------------
% 1.82/0.61  % (17876)Refutation not found, incomplete strategy% (17876)------------------------------
% 1.82/0.61  % (17876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (17876)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.61  
% 1.82/0.61  % (17876)Memory used [KB]: 10618
% 1.82/0.61  % (17876)Time elapsed: 0.182 s
% 1.82/0.61  % (17876)------------------------------
% 1.82/0.61  % (17876)------------------------------
% 1.82/0.61  % (17879)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.82/0.61  % (17887)Refutation not found, incomplete strategy% (17887)------------------------------
% 1.82/0.61  % (17887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (17887)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.61  
% 1.82/0.61  % (17887)Memory used [KB]: 10618
% 1.82/0.61  % (17887)Time elapsed: 0.182 s
% 1.82/0.61  % (17887)------------------------------
% 1.82/0.61  % (17887)------------------------------
% 1.82/0.61  % SZS output start Proof for theBenchmark
% 1.82/0.61  fof(f593,plain,(
% 1.82/0.61    $false),
% 1.82/0.61    inference(avatar_sat_refutation,[],[f52,f57,f62,f72,f77,f592])).
% 1.82/0.61  fof(f592,plain,(
% 1.82/0.61    spl2_2 | ~spl2_5),
% 1.82/0.61    inference(avatar_split_clause,[],[f579,f74,f54])).
% 1.82/0.61  fof(f54,plain,(
% 1.82/0.61    spl2_2 <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.82/0.61  fof(f74,plain,(
% 1.82/0.61    spl2_5 <=> k1_xboole_0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.82/0.61  fof(f579,plain,(
% 1.82/0.61    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl2_5),
% 1.82/0.61    inference(forward_demodulation,[],[f562,f23])).
% 1.82/0.61  fof(f23,plain,(
% 1.82/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f3])).
% 1.82/0.61  fof(f3,axiom,(
% 1.82/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.82/0.61  fof(f562,plain,(
% 1.82/0.61    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k1_xboole_0) | ~spl2_5),
% 1.82/0.61    inference(superposition,[],[f335,f22])).
% 1.82/0.61  fof(f22,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f5])).
% 1.82/0.61  fof(f5,axiom,(
% 1.82/0.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.82/0.61  fof(f335,plain,(
% 1.82/0.61    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = X0) ) | ~spl2_5),
% 1.82/0.61    inference(backward_demodulation,[],[f78,f323])).
% 1.82/0.61  fof(f323,plain,(
% 1.82/0.61    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = X8) ) | ~spl2_5),
% 1.82/0.61    inference(forward_demodulation,[],[f311,f23])).
% 1.82/0.61  fof(f311,plain,(
% 1.82/0.61    ( ! [X8] : (k5_xboole_0(X8,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X8,k1_xboole_0))) ) | ~spl2_5),
% 1.82/0.61    inference(superposition,[],[f266,f25])).
% 1.82/0.61  fof(f25,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f1])).
% 1.82/0.61  fof(f1,axiom,(
% 1.82/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.82/0.61  fof(f266,plain,(
% 1.82/0.61    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | ~spl2_5),
% 1.82/0.61    inference(superposition,[],[f250,f78])).
% 1.82/0.61  fof(f250,plain,(
% 1.82/0.61    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0))) ) | ~spl2_5),
% 1.82/0.61    inference(superposition,[],[f225,f25])).
% 1.82/0.61  fof(f225,plain,(
% 1.82/0.61    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,sK0)) = k5_xboole_0(sK0,X9)) ) | ~spl2_5),
% 1.82/0.61    inference(forward_demodulation,[],[f207,f23])).
% 1.82/0.61  fof(f207,plain,(
% 1.82/0.61    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,sK0)) = k5_xboole_0(sK0,k5_xboole_0(X9,k1_xboole_0))) ) | ~spl2_5),
% 1.82/0.61    inference(superposition,[],[f99,f76])).
% 1.82/0.61  fof(f76,plain,(
% 1.82/0.61    k1_xboole_0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl2_5),
% 1.82/0.61    inference(avatar_component_clause,[],[f74])).
% 1.82/0.61  fof(f99,plain,(
% 1.82/0.61    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(sK0,k5_xboole_0(X2,k5_xboole_0(X3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ) | ~spl2_5),
% 1.82/0.61    inference(superposition,[],[f80,f32])).
% 1.82/0.61  fof(f32,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f4])).
% 1.82/0.61  fof(f4,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.82/0.61  fof(f80,plain,(
% 1.82/0.61    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ) | ~spl2_5),
% 1.82/0.61    inference(superposition,[],[f78,f25])).
% 1.82/0.61  fof(f78,plain,(
% 1.82/0.61    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) ) | ~spl2_5),
% 1.82/0.61    inference(superposition,[],[f32,f76])).
% 1.82/0.61  fof(f77,plain,(
% 1.82/0.61    ~spl2_4 | spl2_5 | ~spl2_3),
% 1.82/0.61    inference(avatar_split_clause,[],[f63,f59,f74,f69])).
% 1.82/0.61  fof(f69,plain,(
% 1.82/0.61    spl2_4 <=> r2_hidden(sK1,sK0)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.82/0.61  fof(f59,plain,(
% 1.82/0.61    spl2_3 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.82/0.61  fof(f63,plain,(
% 1.82/0.61    k1_xboole_0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,sK0) | ~spl2_3),
% 1.82/0.61    inference(superposition,[],[f61,f45])).
% 1.82/0.61  fof(f45,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f28,f42,f42])).
% 1.82/0.61  fof(f42,plain,(
% 1.82/0.61    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f24,f41])).
% 1.82/0.61  fof(f41,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f26,f40])).
% 1.82/0.61  fof(f40,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f31,f39])).
% 1.82/0.61  fof(f39,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f33,f38])).
% 1.82/0.61  fof(f38,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f34,f37])).
% 1.82/0.61  fof(f37,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f35,f36])).
% 1.82/0.61  fof(f36,plain,(
% 1.82/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f12])).
% 1.82/0.61  fof(f12,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.82/0.61  fof(f35,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f11])).
% 1.82/0.61  fof(f11,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.82/0.61  fof(f34,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f10])).
% 1.82/0.61  fof(f10,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.82/0.61  fof(f33,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f9])).
% 1.82/0.61  fof(f9,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.82/0.61  fof(f31,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f8])).
% 1.82/0.61  fof(f8,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.82/0.61  fof(f26,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f7])).
% 1.82/0.61  fof(f7,axiom,(
% 1.82/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.82/0.61  fof(f24,plain,(
% 1.82/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f6])).
% 1.82/0.61  fof(f6,axiom,(
% 1.82/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.82/0.61  fof(f28,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f18])).
% 1.82/0.61  fof(f18,plain,(
% 1.82/0.61    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.82/0.61    inference(ennf_transformation,[],[f13])).
% 1.82/0.61  fof(f13,axiom,(
% 1.82/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.82/0.61  fof(f61,plain,(
% 1.82/0.61    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl2_3),
% 1.82/0.61    inference(avatar_component_clause,[],[f59])).
% 1.82/0.61  fof(f72,plain,(
% 1.82/0.61    spl2_4 | spl2_1 | ~spl2_3),
% 1.82/0.61    inference(avatar_split_clause,[],[f64,f59,f49,f69])).
% 1.82/0.61  fof(f49,plain,(
% 1.82/0.61    spl2_1 <=> k1_xboole_0 = sK0),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.82/0.61  fof(f64,plain,(
% 1.82/0.61    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0) | ~spl2_3),
% 1.82/0.61    inference(superposition,[],[f61,f47])).
% 1.82/0.61  fof(f47,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f29,f27,f42])).
% 1.82/0.61  fof(f27,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f2])).
% 1.82/0.61  fof(f2,axiom,(
% 1.82/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.82/0.61  fof(f29,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f14])).
% 1.82/0.61  fof(f14,axiom,(
% 1.82/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.82/0.61  fof(f62,plain,(
% 1.82/0.61    spl2_3),
% 1.82/0.61    inference(avatar_split_clause,[],[f44,f59])).
% 1.82/0.61  fof(f44,plain,(
% 1.82/0.61    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.82/0.61    inference(definition_unfolding,[],[f19,f27,f42])).
% 1.82/0.61  fof(f19,plain,(
% 1.82/0.61    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.82/0.61    inference(cnf_transformation,[],[f17])).
% 1.82/0.61  fof(f17,plain,(
% 1.82/0.61    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.82/0.61    inference(ennf_transformation,[],[f16])).
% 1.82/0.61  fof(f16,negated_conjecture,(
% 1.82/0.61    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.82/0.61    inference(negated_conjecture,[],[f15])).
% 1.82/0.61  fof(f15,conjecture,(
% 1.82/0.61    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 1.82/0.61  fof(f57,plain,(
% 1.82/0.61    ~spl2_2),
% 1.82/0.61    inference(avatar_split_clause,[],[f43,f54])).
% 1.82/0.61  fof(f43,plain,(
% 1.82/0.61    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.82/0.61    inference(definition_unfolding,[],[f21,f42])).
% 1.82/0.61  fof(f21,plain,(
% 1.82/0.61    sK0 != k1_tarski(sK1)),
% 1.82/0.61    inference(cnf_transformation,[],[f17])).
% 1.82/0.61  % (17886)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.82/0.61  fof(f52,plain,(
% 1.82/0.61    ~spl2_1),
% 1.82/0.61    inference(avatar_split_clause,[],[f20,f49])).
% 1.82/0.61  fof(f20,plain,(
% 1.82/0.61    k1_xboole_0 != sK0),
% 1.82/0.61    inference(cnf_transformation,[],[f17])).
% 1.82/0.61  % SZS output end Proof for theBenchmark
% 1.82/0.61  % (17889)------------------------------
% 1.82/0.61  % (17889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (17889)Termination reason: Refutation
% 1.82/0.61  
% 1.82/0.61  % (17889)Memory used [KB]: 11001
% 1.82/0.61  % (17889)Time elapsed: 0.181 s
% 1.82/0.61  % (17889)------------------------------
% 1.82/0.61  % (17889)------------------------------
% 1.82/0.61  % (17866)Success in time 0.246 s
%------------------------------------------------------------------------------
