%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:35 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 166 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  134 ( 299 expanded)
%              Number of equality atoms :   47 (  91 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3543,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f1081,f3542])).

fof(f3542,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f3541])).

fof(f3541,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f46,f3526])).

fof(f3526,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f34,f3341])).

fof(f3341,plain,(
    sK0 = k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3340,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3340,plain,(
    k5_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3339,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f3339,plain,(
    k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f3329,f747])).

fof(f747,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f41,f35])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3329,plain,(
    k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f118,f1246])).

fof(f1246,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f86,f1134])).

fof(f1134,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1114,f35])).

fof(f1114,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f118,f1070])).

fof(f1070,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1055,f85])).

fof(f85,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1055,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f847,f86])).

fof(f847,plain,(
    ! [X28] : k3_xboole_0(sK0,k3_xboole_0(k4_xboole_0(sK1,sK2),X28)) = k3_xboole_0(sK0,X28) ),
    inference(superposition,[],[f42,f85])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f40,f34])).

fof(f118,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f46,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1081,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f1075])).

fof(f1075,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f1069,f150])).

fof(f150,plain,(
    ! [X3] : r1_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f33,f128])).

fof(f128,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7) ),
    inference(forward_demodulation,[],[f121,f30])).

fof(f121,plain,(
    ! [X7] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f37,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f36,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f33,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1069,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl5_2 ),
    inference(backward_demodulation,[],[f655,f1068])).

fof(f1068,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f1054,f29])).

fof(f1054,plain,(
    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f847,f96])).

fof(f96,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f68,f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f25])).

fof(f25,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f655,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2))
    | spl5_2 ),
    inference(resolution,[],[f308,f50])).

fof(f50,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f308,plain,(
    ! [X4,X5] :
      ( r1_xboole_0(X4,X5)
      | ~ r1_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f38,f154])).

fof(f154,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X1,X1) ) ),
    inference(superposition,[],[f70,f144])).

fof(f144,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f142,f40])).

fof(f142,plain,(
    ! [X2] : r1_tarski(X2,X2) ),
    inference(superposition,[],[f34,f126])).

fof(f126,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f117,f31])).

fof(f117,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f37,f29])).

fof(f70,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X3,X2))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f39,f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f28,f48,f44])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:40:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.47  % (31504)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.47  % (31503)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.48  % (31519)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.48  % (31510)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.49  % (31514)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.49  % (31511)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.49  % (31512)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.49  % (31502)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.50  % (31509)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.50  % (31505)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.50  % (31516)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.51  % (31507)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.51  % (31513)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.51  % (31517)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.52  % (31508)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.52  % (31515)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.52  % (31518)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.27/0.53  % (31506)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.47/0.63  % (31518)Refutation found. Thanks to Tanya!
% 1.47/0.63  % SZS status Theorem for theBenchmark
% 1.47/0.63  % SZS output start Proof for theBenchmark
% 1.47/0.65  fof(f3543,plain,(
% 1.47/0.65    $false),
% 1.47/0.65    inference(avatar_sat_refutation,[],[f51,f1081,f3542])).
% 1.47/0.65  fof(f3542,plain,(
% 1.47/0.65    spl5_1),
% 1.47/0.65    inference(avatar_contradiction_clause,[],[f3541])).
% 1.47/0.65  fof(f3541,plain,(
% 1.47/0.65    $false | spl5_1),
% 1.47/0.65    inference(subsumption_resolution,[],[f46,f3526])).
% 1.47/0.65  fof(f3526,plain,(
% 1.47/0.65    r1_tarski(sK0,sK1)),
% 1.47/0.65    inference(superposition,[],[f34,f3341])).
% 1.47/0.65  fof(f3341,plain,(
% 1.47/0.65    sK0 = k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.47/0.65    inference(forward_demodulation,[],[f3340,f31])).
% 1.47/0.65  fof(f31,plain,(
% 1.47/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.47/0.65    inference(cnf_transformation,[],[f10])).
% 1.47/0.65  fof(f10,axiom,(
% 1.47/0.65    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.47/0.65  fof(f3340,plain,(
% 1.47/0.65    k5_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.47/0.65    inference(forward_demodulation,[],[f3339,f30])).
% 1.47/0.65  fof(f30,plain,(
% 1.47/0.65    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.47/0.65    inference(cnf_transformation,[],[f13])).
% 1.47/0.65  fof(f13,axiom,(
% 1.47/0.65    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.47/0.65  fof(f3339,plain,(
% 1.47/0.65    k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 1.47/0.65    inference(forward_demodulation,[],[f3329,f747])).
% 1.47/0.65  fof(f747,plain,(
% 1.47/0.65    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 1.47/0.65    inference(superposition,[],[f41,f35])).
% 1.47/0.65  fof(f35,plain,(
% 1.47/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.47/0.65    inference(cnf_transformation,[],[f2])).
% 1.47/0.65  fof(f2,axiom,(
% 1.47/0.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.47/0.65  fof(f41,plain,(
% 1.47/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.47/0.65    inference(cnf_transformation,[],[f12])).
% 1.47/0.65  fof(f12,axiom,(
% 1.47/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.47/0.65  fof(f3329,plain,(
% 1.47/0.65    k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.47/0.65    inference(superposition,[],[f118,f1246])).
% 1.47/0.65  fof(f1246,plain,(
% 1.47/0.65    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.47/0.65    inference(superposition,[],[f86,f1134])).
% 1.47/0.65  fof(f1134,plain,(
% 1.47/0.65    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1)),
% 1.47/0.65    inference(forward_demodulation,[],[f1114,f35])).
% 1.47/0.65  fof(f1114,plain,(
% 1.47/0.65    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK0)),
% 1.47/0.65    inference(superposition,[],[f118,f1070])).
% 1.47/0.65  fof(f1070,plain,(
% 1.47/0.65    sK0 = k3_xboole_0(sK0,sK1)),
% 1.47/0.65    inference(forward_demodulation,[],[f1055,f85])).
% 1.47/0.65  fof(f85,plain,(
% 1.47/0.65    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.47/0.65    inference(resolution,[],[f40,f27])).
% 1.47/0.65  fof(f27,plain,(
% 1.47/0.65    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.47/0.65    inference(cnf_transformation,[],[f22])).
% 1.47/0.65  fof(f22,plain,(
% 1.47/0.65    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.47/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21])).
% 1.47/0.65  fof(f21,plain,(
% 1.47/0.65    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.47/0.65    introduced(choice_axiom,[])).
% 1.47/0.65  fof(f17,plain,(
% 1.47/0.65    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.47/0.65    inference(ennf_transformation,[],[f15])).
% 1.47/0.65  fof(f15,negated_conjecture,(
% 1.47/0.65    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.47/0.65    inference(negated_conjecture,[],[f14])).
% 1.47/0.65  fof(f14,conjecture,(
% 1.47/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.47/0.65  fof(f40,plain,(
% 1.47/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.47/0.65    inference(cnf_transformation,[],[f20])).
% 1.47/0.65  fof(f20,plain,(
% 1.47/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.47/0.65    inference(ennf_transformation,[],[f7])).
% 1.47/0.65  fof(f7,axiom,(
% 1.47/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.47/0.65  fof(f1055,plain,(
% 1.47/0.65    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK1)),
% 1.47/0.65    inference(superposition,[],[f847,f86])).
% 1.47/0.65  fof(f847,plain,(
% 1.47/0.65    ( ! [X28] : (k3_xboole_0(sK0,k3_xboole_0(k4_xboole_0(sK1,sK2),X28)) = k3_xboole_0(sK0,X28)) )),
% 1.47/0.65    inference(superposition,[],[f42,f85])).
% 1.47/0.65  fof(f42,plain,(
% 1.47/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.47/0.65    inference(cnf_transformation,[],[f6])).
% 1.47/0.65  fof(f6,axiom,(
% 1.47/0.65    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.47/0.65  fof(f86,plain,(
% 1.47/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.47/0.65    inference(resolution,[],[f40,f34])).
% 1.47/0.65  fof(f118,plain,(
% 1.47/0.65    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.47/0.65    inference(superposition,[],[f37,f36])).
% 1.47/0.65  fof(f36,plain,(
% 1.47/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.47/0.65    inference(cnf_transformation,[],[f1])).
% 1.47/0.65  fof(f1,axiom,(
% 1.47/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.47/0.65  fof(f37,plain,(
% 1.47/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.47/0.65    inference(cnf_transformation,[],[f5])).
% 1.47/0.65  fof(f5,axiom,(
% 1.47/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.47/0.65  fof(f34,plain,(
% 1.47/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.47/0.65    inference(cnf_transformation,[],[f9])).
% 1.47/0.65  fof(f9,axiom,(
% 1.47/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.47/0.65  fof(f46,plain,(
% 1.47/0.65    ~r1_tarski(sK0,sK1) | spl5_1),
% 1.47/0.65    inference(avatar_component_clause,[],[f44])).
% 1.47/0.65  fof(f44,plain,(
% 1.47/0.65    spl5_1 <=> r1_tarski(sK0,sK1)),
% 1.47/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.47/0.65  fof(f1081,plain,(
% 1.47/0.65    spl5_2),
% 1.47/0.65    inference(avatar_contradiction_clause,[],[f1075])).
% 1.47/0.65  fof(f1075,plain,(
% 1.47/0.65    $false | spl5_2),
% 1.47/0.65    inference(resolution,[],[f1069,f150])).
% 1.47/0.65  fof(f150,plain,(
% 1.47/0.65    ( ! [X3] : (r1_xboole_0(k1_xboole_0,X3)) )),
% 1.47/0.65    inference(superposition,[],[f33,f128])).
% 1.47/0.65  fof(f128,plain,(
% 1.47/0.65    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7)) )),
% 1.47/0.65    inference(forward_demodulation,[],[f121,f30])).
% 1.47/0.65  fof(f121,plain,(
% 1.47/0.65    ( ! [X7] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X7)) )),
% 1.47/0.65    inference(superposition,[],[f37,f60])).
% 1.47/0.65  fof(f60,plain,(
% 1.47/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.47/0.65    inference(superposition,[],[f36,f29])).
% 1.47/0.65  fof(f29,plain,(
% 1.47/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.47/0.65    inference(cnf_transformation,[],[f8])).
% 1.47/0.65  fof(f8,axiom,(
% 1.47/0.65    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.47/0.65  fof(f33,plain,(
% 1.47/0.65    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.47/0.65    inference(cnf_transformation,[],[f11])).
% 1.47/0.65  fof(f11,axiom,(
% 1.47/0.65    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.47/0.65  fof(f1069,plain,(
% 1.47/0.65    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl5_2),
% 1.47/0.65    inference(backward_demodulation,[],[f655,f1068])).
% 1.47/0.65  fof(f1068,plain,(
% 1.47/0.65    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.47/0.65    inference(forward_demodulation,[],[f1054,f29])).
% 1.47/0.65  fof(f1054,plain,(
% 1.47/0.65    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2)),
% 1.47/0.65    inference(superposition,[],[f847,f96])).
% 1.47/0.65  fof(f96,plain,(
% 1.47/0.65    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.47/0.65    inference(resolution,[],[f68,f33])).
% 1.47/0.65  fof(f68,plain,(
% 1.47/0.65    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.47/0.65    inference(resolution,[],[f39,f32])).
% 1.47/0.65  fof(f32,plain,(
% 1.47/0.65    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.47/0.65    inference(cnf_transformation,[],[f24])).
% 1.47/0.65  fof(f24,plain,(
% 1.47/0.65    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.47/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f23])).
% 1.47/0.65  fof(f23,plain,(
% 1.47/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.47/0.65    introduced(choice_axiom,[])).
% 1.47/0.65  fof(f18,plain,(
% 1.47/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.47/0.65    inference(ennf_transformation,[],[f4])).
% 1.47/0.65  fof(f4,axiom,(
% 1.47/0.65    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.47/0.65  fof(f39,plain,(
% 1.47/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.47/0.65    inference(cnf_transformation,[],[f26])).
% 1.47/0.65  fof(f26,plain,(
% 1.47/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.47/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f25])).
% 1.47/0.65  fof(f25,plain,(
% 1.47/0.65    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.47/0.65    introduced(choice_axiom,[])).
% 1.47/0.65  fof(f19,plain,(
% 1.47/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.47/0.65    inference(ennf_transformation,[],[f16])).
% 1.47/0.65  fof(f16,plain,(
% 1.47/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.65    inference(rectify,[],[f3])).
% 1.47/0.65  fof(f3,axiom,(
% 1.47/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.47/0.65  fof(f655,plain,(
% 1.47/0.65    ~r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)) | spl5_2),
% 1.47/0.65    inference(resolution,[],[f308,f50])).
% 1.47/0.65  fof(f50,plain,(
% 1.47/0.65    ~r1_xboole_0(sK0,sK2) | spl5_2),
% 1.47/0.65    inference(avatar_component_clause,[],[f48])).
% 1.47/0.65  fof(f48,plain,(
% 1.47/0.65    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 1.47/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.47/0.65  fof(f308,plain,(
% 1.47/0.65    ( ! [X4,X5] : (r1_xboole_0(X4,X5) | ~r1_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 1.47/0.65    inference(resolution,[],[f38,f154])).
% 1.47/0.65  fof(f154,plain,(
% 1.47/0.65    ( ! [X2,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X1,X1)) )),
% 1.47/0.65    inference(superposition,[],[f70,f144])).
% 1.47/0.65  fof(f144,plain,(
% 1.47/0.65    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.47/0.65    inference(resolution,[],[f142,f40])).
% 1.47/0.65  fof(f142,plain,(
% 1.47/0.65    ( ! [X2] : (r1_tarski(X2,X2)) )),
% 1.47/0.65    inference(superposition,[],[f34,f126])).
% 1.47/0.65  fof(f126,plain,(
% 1.47/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.47/0.65    inference(forward_demodulation,[],[f117,f31])).
% 1.47/0.65  fof(f117,plain,(
% 1.47/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.47/0.65    inference(superposition,[],[f37,f29])).
% 1.47/0.65  fof(f70,plain,(
% 1.47/0.65    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X3,X2)) | ~r1_xboole_0(X2,X3)) )),
% 1.47/0.65    inference(superposition,[],[f39,f36])).
% 1.47/0.65  fof(f38,plain,(
% 1.47/0.65    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.47/0.65    inference(cnf_transformation,[],[f26])).
% 1.47/0.65  fof(f51,plain,(
% 1.47/0.65    ~spl5_1 | ~spl5_2),
% 1.47/0.65    inference(avatar_split_clause,[],[f28,f48,f44])).
% 1.47/0.65  fof(f28,plain,(
% 1.47/0.65    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.47/0.65    inference(cnf_transformation,[],[f22])).
% 1.47/0.65  % SZS output end Proof for theBenchmark
% 1.47/0.65  % (31518)------------------------------
% 1.47/0.65  % (31518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.65  % (31518)Termination reason: Refutation
% 1.47/0.65  
% 1.47/0.65  % (31518)Memory used [KB]: 7931
% 1.47/0.65  % (31518)Time elapsed: 0.210 s
% 1.47/0.65  % (31518)------------------------------
% 1.47/0.65  % (31518)------------------------------
% 2.25/0.65  % (31501)Success in time 0.28 s
%------------------------------------------------------------------------------
