%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:39 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 282 expanded)
%              Number of leaves         :   14 (  82 expanded)
%              Depth                    :   20
%              Number of atoms          :  132 ( 525 expanded)
%              Number of equality atoms :   57 ( 248 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1578,plain,(
    $false ),
    inference(global_subsumption,[],[f1410,f1577])).

fof(f1577,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f1476,f1385])).

fof(f1385,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f1384,f100])).

fof(f100,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f93,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f93,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f88,f83])).

fof(f83,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(k1_xboole_0,X4) ) ),
    inference(superposition,[],[f24,f32])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f24,f83])).

fof(f1384,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f1324,f417])).

fof(f417,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f392,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f392,plain,(
    r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f383,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f383,plain,(
    ~ r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f314,f78])).

fof(f78,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f24,f32])).

fof(f314,plain,(
    ! [X0,X1] : ~ r2_hidden(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),X1)) ),
    inference(unit_resulting_resolution,[],[f250,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f250,plain,(
    ! [X0,X1] : ~ sP3(sK1,X0,k4_xboole_0(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f242,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f242,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f240,f63])).

fof(f240,plain,(
    ! [X0] : ~ sP3(sK1,X0,sK0) ),
    inference(unit_resulting_resolution,[],[f233,f37])).

fof(f233,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f224,f67])).

fof(f67,plain,(
    ! [X4,X0,X1] : sP5(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f224,plain,(
    ! [X0] :
      ( ~ sP5(X0,sK1,sK1,sK1)
      | ~ r2_hidden(sK1,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f66,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(sK1,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f102,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f102,plain,(
    ! [X0] :
      ( sP3(X0,k2_enumset1(sK1,sK1,sK1,sK1),sK0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK1,sK0) ) ),
    inference(superposition,[],[f63,f55])).

fof(f55,plain,
    ( sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(definition_unfolding,[],[f20,f52])).

fof(f20,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f47,f34])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1324,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f328,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f56,f32])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f328,plain,(
    r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f239,f98])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f88,f31])).

fof(f239,plain,(
    r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f233,f57])).

fof(f1476,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f239,f182])).

fof(f182,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X2) = k4_xboole_0(X3,k4_xboole_0(X3,X2))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f56,f31])).

fof(f1410,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f1033,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1033,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f238,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X0,X1))
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(forward_demodulation,[],[f172,f22])).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f172,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
      | ~ r1_tarski(X0,k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f53,f32])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f238,plain,(
    sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f233,f54])).

fof(f54,plain,
    ( sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,sK0) ),
    inference(definition_unfolding,[],[f21,f52])).

fof(f21,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (28072)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (28065)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (28070)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (28089)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (28071)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (28073)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.23/0.52  % (28064)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.52  % (28066)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.52  % (28067)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.23/0.52  % (28081)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.53  % (28064)Refutation not found, incomplete strategy% (28064)------------------------------
% 1.23/0.53  % (28064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (28064)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (28064)Memory used [KB]: 10618
% 1.23/0.53  % (28064)Time elapsed: 0.116 s
% 1.23/0.53  % (28064)------------------------------
% 1.23/0.53  % (28064)------------------------------
% 1.23/0.53  % (28074)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.23/0.53  % (28092)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.23/0.53  % (28082)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.23/0.53  % (28084)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.53  % (28068)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.54  % (28088)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.23/0.54  % (28076)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.54  % (28090)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.23/0.54  % (28091)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.23/0.54  % (28085)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.23/0.54  % (28063)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.54  % (28085)Refutation not found, incomplete strategy% (28085)------------------------------
% 1.23/0.54  % (28085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (28085)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (28085)Memory used [KB]: 10746
% 1.23/0.54  % (28085)Time elapsed: 0.094 s
% 1.23/0.54  % (28085)------------------------------
% 1.23/0.54  % (28085)------------------------------
% 1.23/0.54  % (28083)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.23/0.54  % (28077)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.54  % (28062)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.54  % (28071)Refutation not found, incomplete strategy% (28071)------------------------------
% 1.23/0.54  % (28071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (28071)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (28071)Memory used [KB]: 10618
% 1.23/0.54  % (28071)Time elapsed: 0.137 s
% 1.23/0.54  % (28071)------------------------------
% 1.23/0.54  % (28071)------------------------------
% 1.23/0.54  % (28075)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.55  % (28087)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.23/0.55  % (28080)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.23/0.55  % (28086)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.55  % (28080)Refutation not found, incomplete strategy% (28080)------------------------------
% 1.45/0.55  % (28080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (28080)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (28080)Memory used [KB]: 10618
% 1.45/0.55  % (28080)Time elapsed: 0.144 s
% 1.45/0.55  % (28080)------------------------------
% 1.45/0.55  % (28080)------------------------------
% 1.45/0.55  % (28079)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (28078)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.63  % (28087)Refutation found. Thanks to Tanya!
% 1.45/0.63  % SZS status Theorem for theBenchmark
% 1.45/0.63  % SZS output start Proof for theBenchmark
% 1.45/0.63  fof(f1578,plain,(
% 1.45/0.63    $false),
% 1.45/0.63    inference(global_subsumption,[],[f1410,f1577])).
% 1.45/0.63  fof(f1577,plain,(
% 1.45/0.63    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.45/0.63    inference(forward_demodulation,[],[f1476,f1385])).
% 1.45/0.63  fof(f1385,plain,(
% 1.45/0.63    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.45/0.63    inference(forward_demodulation,[],[f1384,f100])).
% 1.45/0.63  fof(f100,plain,(
% 1.45/0.63    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f93,f32])).
% 1.45/0.63  fof(f32,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f3])).
% 1.45/0.63  fof(f3,axiom,(
% 1.45/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.45/0.63  fof(f93,plain,(
% 1.45/0.63    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f88,f83])).
% 1.45/0.63  fof(f83,plain,(
% 1.45/0.63    ( ! [X4,X5] : (~r1_tarski(X4,X5) | r1_tarski(k1_xboole_0,X4)) )),
% 1.45/0.63    inference(superposition,[],[f24,f32])).
% 1.45/0.63  fof(f24,plain,(
% 1.45/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f5])).
% 1.45/0.63  fof(f5,axiom,(
% 1.45/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.45/0.63  fof(f88,plain,(
% 1.45/0.63    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1))) )),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f24,f83])).
% 1.45/0.63  fof(f1384,plain,(
% 1.45/0.63    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.45/0.63    inference(forward_demodulation,[],[f1324,f417])).
% 1.45/0.63  fof(f417,plain,(
% 1.45/0.63    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f392,f31])).
% 1.45/0.63  fof(f31,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f9])).
% 1.45/0.63  fof(f9,axiom,(
% 1.45/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.45/0.63  fof(f392,plain,(
% 1.45/0.63    r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f383,f57])).
% 1.45/0.63  fof(f57,plain,(
% 1.45/0.63    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f29,f52])).
% 1.45/0.63  fof(f52,plain,(
% 1.45/0.63    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f23,f51])).
% 1.45/0.63  fof(f51,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f26,f34])).
% 1.45/0.63  fof(f34,plain,(
% 1.45/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f13])).
% 1.45/0.63  fof(f13,axiom,(
% 1.45/0.63    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.63  fof(f26,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f12])).
% 1.45/0.63  fof(f12,axiom,(
% 1.45/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.63  fof(f23,plain,(
% 1.45/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f11])).
% 1.45/0.63  fof(f11,axiom,(
% 1.45/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.63  fof(f29,plain,(
% 1.45/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f18])).
% 1.45/0.63  fof(f18,plain,(
% 1.45/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.45/0.63    inference(ennf_transformation,[],[f14])).
% 1.45/0.63  fof(f14,axiom,(
% 1.45/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.45/0.63  fof(f383,plain,(
% 1.45/0.63    ~r2_hidden(sK1,k1_xboole_0)),
% 1.45/0.63    inference(superposition,[],[f314,f78])).
% 1.45/0.63  fof(f78,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f24,f32])).
% 1.45/0.63  fof(f314,plain,(
% 1.45/0.63    ( ! [X0,X1] : (~r2_hidden(sK1,k4_xboole_0(k4_xboole_0(sK0,X0),X1))) )),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f250,f63])).
% 1.45/0.64  fof(f63,plain,(
% 1.45/0.64    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP3(X3,X1,X0)) )),
% 1.45/0.64    inference(equality_resolution,[],[f40])).
% 1.45/0.64  fof(f40,plain,(
% 1.45/0.64    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.45/0.64    inference(cnf_transformation,[],[f2])).
% 1.45/0.64  fof(f2,axiom,(
% 1.45/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.45/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.45/0.64  fof(f250,plain,(
% 1.45/0.64    ( ! [X0,X1] : (~sP3(sK1,X0,k4_xboole_0(sK0,X1))) )),
% 1.45/0.64    inference(unit_resulting_resolution,[],[f242,f37])).
% 1.45/0.64  fof(f37,plain,(
% 1.45/0.64    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.45/0.64    inference(cnf_transformation,[],[f2])).
% 1.45/0.64  fof(f242,plain,(
% 1.45/0.64    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(sK0,X0))) )),
% 1.45/0.64    inference(unit_resulting_resolution,[],[f240,f63])).
% 2.05/0.65  fof(f240,plain,(
% 2.05/0.65    ( ! [X0] : (~sP3(sK1,X0,sK0)) )),
% 2.05/0.65    inference(unit_resulting_resolution,[],[f233,f37])).
% 2.05/0.65  fof(f233,plain,(
% 2.05/0.65    ~r2_hidden(sK1,sK0)),
% 2.05/0.65    inference(duplicate_literal_removal,[],[f228])).
% 2.05/0.65  fof(f228,plain,(
% 2.05/0.65    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,sK0)),
% 2.05/0.65    inference(resolution,[],[f224,f67])).
% 2.05/0.65  fof(f67,plain,(
% 2.05/0.65    ( ! [X4,X0,X1] : (sP5(X4,X4,X1,X0)) )),
% 2.05/0.65    inference(equality_resolution,[],[f45])).
% 2.05/0.65  fof(f45,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP5(X4,X2,X1,X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f19])).
% 2.05/0.65  fof(f19,plain,(
% 2.05/0.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.05/0.65    inference(ennf_transformation,[],[f10])).
% 2.05/0.65  fof(f10,axiom,(
% 2.05/0.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.05/0.65  fof(f224,plain,(
% 2.05/0.65    ( ! [X0] : (~sP5(X0,sK1,sK1,sK1) | ~r2_hidden(sK1,sK0) | ~r2_hidden(X0,sK0)) )),
% 2.05/0.65    inference(resolution,[],[f66,f127])).
% 2.05/0.65  fof(f127,plain,(
% 2.05/0.65    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,sK0) | ~r2_hidden(X0,sK0)) )),
% 2.05/0.65    inference(resolution,[],[f102,f38])).
% 2.05/0.65  fof(f38,plain,(
% 2.05/0.65    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f2])).
% 2.05/0.65  fof(f102,plain,(
% 2.05/0.65    ( ! [X0] : (sP3(X0,k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK1,sK0)) )),
% 2.05/0.65    inference(superposition,[],[f63,f55])).
% 2.05/0.65  fof(f55,plain,(
% 2.05/0.65    sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,sK0)),
% 2.05/0.65    inference(definition_unfolding,[],[f20,f52])).
% 2.05/0.65  fof(f20,plain,(
% 2.05/0.65    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.05/0.65    inference(cnf_transformation,[],[f17])).
% 2.05/0.65  fof(f17,plain,(
% 2.05/0.65    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 2.05/0.65    inference(ennf_transformation,[],[f16])).
% 2.05/0.65  fof(f16,negated_conjecture,(
% 2.05/0.65    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.05/0.65    inference(negated_conjecture,[],[f15])).
% 2.05/0.65  fof(f15,conjecture,(
% 2.05/0.65    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.05/0.65  fof(f66,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 2.05/0.65    inference(equality_resolution,[],[f62])).
% 2.05/0.65  fof(f62,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.05/0.65    inference(definition_unfolding,[],[f47,f34])).
% 2.05/0.65  fof(f47,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.05/0.65    inference(cnf_transformation,[],[f19])).
% 2.05/0.65  fof(f1324,plain,(
% 2.05/0.65    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0))),
% 2.05/0.65    inference(unit_resulting_resolution,[],[f328,f181])).
% 2.05/0.65  fof(f181,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(superposition,[],[f56,f32])).
% 2.05/0.65  fof(f56,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.05/0.65    inference(definition_unfolding,[],[f25,f27,f27])).
% 2.05/0.65  fof(f27,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f6])).
% 2.05/0.65  fof(f6,axiom,(
% 2.05/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.05/0.65  fof(f25,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f1])).
% 2.05/0.65  fof(f1,axiom,(
% 2.05/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.05/0.65  fof(f328,plain,(
% 2.05/0.65    r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.05/0.65    inference(unit_resulting_resolution,[],[f239,f98])).
% 2.05/0.65  fof(f98,plain,(
% 2.05/0.65    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_tarski(k1_xboole_0,X2)) )),
% 2.05/0.65    inference(superposition,[],[f88,f31])).
% 2.05/0.65  fof(f239,plain,(
% 2.05/0.65    r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 2.05/0.65    inference(unit_resulting_resolution,[],[f233,f57])).
% 2.05/0.65  fof(f1476,plain,(
% 2.05/0.65    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.05/0.65    inference(unit_resulting_resolution,[],[f239,f182])).
% 2.05/0.65  fof(f182,plain,(
% 2.05/0.65    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(X3,k4_xboole_0(X3,X2)) | ~r1_xboole_0(X2,X3)) )),
% 2.05/0.65    inference(superposition,[],[f56,f31])).
% 2.05/0.65  fof(f1410,plain,(
% 2.05/0.65    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 2.05/0.65    inference(unit_resulting_resolution,[],[f1033,f33])).
% 2.05/0.65  fof(f33,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f3])).
% 2.05/0.65  fof(f1033,plain,(
% 2.05/0.65    ~r1_tarski(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 2.05/0.65    inference(unit_resulting_resolution,[],[f238,f176])).
% 2.05/0.65  fof(f176,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X0,X1)) | k4_xboole_0(X0,X1) = X0) )),
% 2.05/0.65    inference(forward_demodulation,[],[f172,f22])).
% 2.05/0.65  fof(f22,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.05/0.65    inference(cnf_transformation,[],[f8])).
% 2.05/0.65  fof(f8,axiom,(
% 2.05/0.65    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.05/0.65  fof(f172,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_tarski(X0,k4_xboole_0(X0,X1))) )),
% 2.05/0.65    inference(superposition,[],[f53,f32])).
% 2.05/0.65  fof(f53,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.05/0.65    inference(definition_unfolding,[],[f28,f27])).
% 2.05/0.65  fof(f28,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f4])).
% 2.05/0.65  fof(f4,axiom,(
% 2.05/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.05/0.65  fof(f238,plain,(
% 2.05/0.65    sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.05/0.65    inference(unit_resulting_resolution,[],[f233,f54])).
% 2.05/0.65  fof(f54,plain,(
% 2.05/0.65    sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK1,sK0)),
% 2.05/0.65    inference(definition_unfolding,[],[f21,f52])).
% 2.05/0.65  fof(f21,plain,(
% 2.05/0.65    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.05/0.65    inference(cnf_transformation,[],[f17])).
% 2.05/0.65  % SZS output end Proof for theBenchmark
% 2.05/0.65  % (28087)------------------------------
% 2.05/0.65  % (28087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.65  % (28087)Termination reason: Refutation
% 2.05/0.65  
% 2.05/0.65  % (28087)Memory used [KB]: 7547
% 2.05/0.65  % (28087)Time elapsed: 0.217 s
% 2.05/0.65  % (28087)------------------------------
% 2.05/0.65  % (28087)------------------------------
% 2.05/0.65  % (28061)Success in time 0.287 s
%------------------------------------------------------------------------------
