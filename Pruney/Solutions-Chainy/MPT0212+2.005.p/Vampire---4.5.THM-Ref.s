%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:54 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 144 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 203 expanded)
%              Number of equality atoms :   58 ( 127 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f559,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f524,f533,f548,f558])).

fof(f558,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f543,f553])).

fof(f553,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_1
    | spl2_2 ),
    inference(forward_demodulation,[],[f522,f519])).

fof(f519,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f522,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f521])).

fof(f521,plain,
    ( spl2_2
  <=> r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f543,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl2_4
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f548,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f73,f544,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f544,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f542])).

fof(f73,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f71,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_xboole_0)
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f62,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f533,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f523,f56,f526,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X0
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X0
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f526,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_2 ),
    inference(resolution,[],[f525,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f525,plain,
    ( r1_tarski(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl2_2 ),
    inference(resolution,[],[f523,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f23,f55])).

fof(f23,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(flattening,[],[f20])).

fof(f20,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f523,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f521])).

fof(f524,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f515,f521,f517])).

fof(f515,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(equality_resolution,[],[f512])).

fof(f512,plain,(
    ! [X5] :
      ( k1_zfmisc_1(k1_xboole_0) != X5
      | r2_hidden(sK1(k1_xboole_0,X5),X5)
      | k1_xboole_0 = sK1(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f56,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | r2_hidden(sK1(X0,X1),X1)
      | sK1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:12:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (25656)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (25643)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (25635)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (25635)Refutation not found, incomplete strategy% (25635)------------------------------
% 0.22/0.52  % (25635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25635)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25635)Memory used [KB]: 1663
% 0.22/0.52  % (25635)Time elapsed: 0.101 s
% 0.22/0.52  % (25635)------------------------------
% 0.22/0.52  % (25635)------------------------------
% 0.22/0.52  % (25647)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (25657)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (25639)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (25649)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (25646)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (25634)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (25637)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (25660)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (25658)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.45/0.55  % (25638)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.45/0.55  % (25641)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.45/0.55  % (25651)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.45/0.55  % (25636)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.45/0.55  % (25642)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.45/0.55  % (25645)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.45/0.55  % (25645)Refutation not found, incomplete strategy% (25645)------------------------------
% 1.45/0.55  % (25645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (25645)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (25645)Memory used [KB]: 6140
% 1.45/0.55  % (25645)Time elapsed: 0.150 s
% 1.45/0.55  % (25645)------------------------------
% 1.45/0.55  % (25645)------------------------------
% 1.45/0.55  % (25647)Refutation found. Thanks to Tanya!
% 1.45/0.55  % SZS status Theorem for theBenchmark
% 1.45/0.55  % SZS output start Proof for theBenchmark
% 1.45/0.55  fof(f559,plain,(
% 1.45/0.55    $false),
% 1.45/0.55    inference(avatar_sat_refutation,[],[f524,f533,f548,f558])).
% 1.45/0.55  fof(f558,plain,(
% 1.45/0.55    ~spl2_1 | spl2_2 | ~spl2_4),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f554])).
% 1.45/0.55  fof(f554,plain,(
% 1.45/0.55    $false | (~spl2_1 | spl2_2 | ~spl2_4)),
% 1.45/0.55    inference(subsumption_resolution,[],[f543,f553])).
% 1.45/0.55  fof(f553,plain,(
% 1.45/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl2_1 | spl2_2)),
% 1.45/0.55    inference(forward_demodulation,[],[f522,f519])).
% 1.45/0.55  fof(f519,plain,(
% 1.45/0.55    k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl2_1),
% 1.45/0.55    inference(avatar_component_clause,[],[f517])).
% 1.45/0.55  fof(f517,plain,(
% 1.45/0.55    spl2_1 <=> k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.45/0.55  fof(f522,plain,(
% 1.45/0.55    ~r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | spl2_2),
% 1.45/0.55    inference(avatar_component_clause,[],[f521])).
% 1.45/0.55  fof(f521,plain,(
% 1.45/0.55    spl2_2 <=> r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.45/0.55  fof(f543,plain,(
% 1.45/0.55    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl2_4),
% 1.45/0.55    inference(avatar_component_clause,[],[f542])).
% 1.45/0.55  fof(f542,plain,(
% 1.45/0.55    spl2_4 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.45/0.55  fof(f548,plain,(
% 1.45/0.55    spl2_4),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f546])).
% 1.45/0.55  fof(f546,plain,(
% 1.45/0.55    $false | spl2_4),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f73,f544,f66])).
% 1.45/0.55  fof(f66,plain,(
% 1.45/0.55    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.45/0.55    inference(equality_resolution,[],[f32])).
% 1.45/0.55  fof(f32,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f18])).
% 1.45/0.55  fof(f18,axiom,(
% 1.45/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.45/0.55  fof(f544,plain,(
% 1.45/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl2_4),
% 1.45/0.55    inference(avatar_component_clause,[],[f542])).
% 1.45/0.55  fof(f73,plain,(
% 1.45/0.55    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.45/0.55    inference(equality_resolution,[],[f72])).
% 1.45/0.55  fof(f72,plain,(
% 1.45/0.55    ( ! [X0] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_xboole_0)) )),
% 1.45/0.55    inference(forward_demodulation,[],[f71,f25])).
% 1.45/0.55  fof(f25,plain,(
% 1.45/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.55    inference(cnf_transformation,[],[f8])).
% 1.45/0.55  fof(f8,axiom,(
% 1.45/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.45/0.55  fof(f71,plain,(
% 1.45/0.55    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(X0,k1_xboole_0) | r1_tarski(X0,k1_xboole_0)) )),
% 1.45/0.55    inference(superposition,[],[f62,f24])).
% 1.45/0.55  fof(f24,plain,(
% 1.45/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f5])).
% 1.45/0.55  fof(f5,axiom,(
% 1.45/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.45/0.55  fof(f62,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f41,f31])).
% 1.45/0.55  fof(f31,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f2])).
% 1.45/0.55  fof(f2,axiom,(
% 1.45/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.55  fof(f41,plain,(
% 1.45/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.45/0.55    inference(cnf_transformation,[],[f1])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.45/0.55  fof(f533,plain,(
% 1.45/0.55    ~spl2_2),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f527])).
% 1.45/0.55  fof(f527,plain,(
% 1.45/0.55    $false | ~spl2_2),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f523,f56,f526,f58])).
% 1.45/0.55  fof(f58,plain,(
% 1.45/0.55    ( ! [X0,X1] : (sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1) )),
% 1.45/0.55    inference(definition_unfolding,[],[f39,f55])).
% 1.45/0.55  fof(f55,plain,(
% 1.45/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f26,f54])).
% 1.45/0.55  fof(f54,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f29,f53])).
% 1.45/0.55  fof(f53,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f42,f52])).
% 1.45/0.55  fof(f52,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f45,f51])).
% 1.45/0.55  fof(f51,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f46,f50])).
% 1.45/0.55  fof(f50,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f47,f48])).
% 1.45/0.55  fof(f48,plain,(
% 1.45/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f17])).
% 1.45/0.55  fof(f17,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.45/0.55  fof(f47,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f16])).
% 1.45/0.55  fof(f16,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.45/0.55  fof(f46,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f15])).
% 1.45/0.55  fof(f15,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.45/0.55  fof(f45,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f14,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.45/0.55  fof(f42,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f13])).
% 1.45/0.55  fof(f13,axiom,(
% 1.45/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.55  fof(f29,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f12])).
% 1.45/0.55  fof(f12,axiom,(
% 1.45/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.55  fof(f26,plain,(
% 1.45/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f11])).
% 1.45/0.55  fof(f11,axiom,(
% 1.45/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.55  fof(f39,plain,(
% 1.45/0.55    ( ! [X0,X1] : (sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f10])).
% 1.45/0.55  fof(f10,axiom,(
% 1.45/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.45/0.55  fof(f526,plain,(
% 1.45/0.55    k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl2_2),
% 1.45/0.55    inference(resolution,[],[f525,f27])).
% 1.45/0.55  fof(f27,plain,(
% 1.45/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.45/0.55    inference(cnf_transformation,[],[f22])).
% 1.45/0.55  fof(f22,plain,(
% 1.45/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.45/0.55    inference(ennf_transformation,[],[f6])).
% 1.45/0.55  fof(f6,axiom,(
% 1.45/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.45/0.55  fof(f525,plain,(
% 1.45/0.55    r1_tarski(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) | ~spl2_2),
% 1.45/0.55    inference(resolution,[],[f523,f65])).
% 1.45/0.55  fof(f65,plain,(
% 1.45/0.55    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.45/0.55    inference(equality_resolution,[],[f33])).
% 1.45/0.55  fof(f33,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f18])).
% 1.45/0.55  fof(f56,plain,(
% 1.45/0.55    k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.45/0.55    inference(definition_unfolding,[],[f23,f55])).
% 1.45/0.55  fof(f23,plain,(
% 1.45/0.55    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 1.45/0.55    inference(cnf_transformation,[],[f21])).
% 1.45/0.55  fof(f21,plain,(
% 1.45/0.55    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 1.45/0.55    inference(flattening,[],[f20])).
% 1.45/0.55  fof(f20,negated_conjecture,(
% 1.45/0.55    ~k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.45/0.55    inference(negated_conjecture,[],[f19])).
% 1.45/0.55  fof(f19,conjecture,(
% 1.45/0.55    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.45/0.55  fof(f523,plain,(
% 1.45/0.55    r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~spl2_2),
% 1.45/0.55    inference(avatar_component_clause,[],[f521])).
% 1.45/0.55  fof(f524,plain,(
% 1.45/0.55    spl2_1 | spl2_2),
% 1.45/0.55    inference(avatar_split_clause,[],[f515,f521,f517])).
% 1.45/0.55  fof(f515,plain,(
% 1.45/0.55    r2_hidden(sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.45/0.55    inference(equality_resolution,[],[f512])).
% 1.45/0.55  fof(f512,plain,(
% 1.45/0.55    ( ! [X5] : (k1_zfmisc_1(k1_xboole_0) != X5 | r2_hidden(sK1(k1_xboole_0,X5),X5) | k1_xboole_0 = sK1(k1_xboole_0,X5)) )),
% 1.45/0.55    inference(superposition,[],[f56,f59])).
% 1.45/0.55  fof(f59,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | r2_hidden(sK1(X0,X1),X1) | sK1(X0,X1) = X0) )),
% 1.45/0.55    inference(definition_unfolding,[],[f38,f55])).
% 1.45/0.55  fof(f38,plain,(
% 1.45/0.55    ( ! [X0,X1] : (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f10])).
% 1.45/0.55  % SZS output end Proof for theBenchmark
% 1.45/0.55  % (25647)------------------------------
% 1.45/0.55  % (25647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (25647)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (25652)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.45/0.55  % (25652)Refutation not found, incomplete strategy% (25652)------------------------------
% 1.45/0.55  % (25652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (25652)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (25652)Memory used [KB]: 1663
% 1.45/0.55  % (25652)Time elapsed: 0.148 s
% 1.45/0.55  % (25652)------------------------------
% 1.45/0.55  % (25652)------------------------------
% 1.45/0.56  % (25662)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.45/0.56  % (25660)Refutation not found, incomplete strategy% (25660)------------------------------
% 1.45/0.56  % (25660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (25660)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (25660)Memory used [KB]: 6140
% 1.45/0.56  % (25660)Time elapsed: 0.146 s
% 1.45/0.56  % (25660)------------------------------
% 1.45/0.56  % (25660)------------------------------
% 1.45/0.56  % (25661)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.45/0.56  % (25651)Refutation not found, incomplete strategy% (25651)------------------------------
% 1.45/0.56  % (25651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (25651)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (25651)Memory used [KB]: 1663
% 1.45/0.56  % (25651)Time elapsed: 0.149 s
% 1.45/0.56  % (25651)------------------------------
% 1.45/0.56  % (25651)------------------------------
% 1.45/0.56  % (25661)Refutation not found, incomplete strategy% (25661)------------------------------
% 1.45/0.56  % (25661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (25661)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (25661)Memory used [KB]: 6140
% 1.45/0.56  % (25661)Time elapsed: 0.148 s
% 1.45/0.56  % (25661)------------------------------
% 1.45/0.56  % (25661)------------------------------
% 1.45/0.56  % (25658)Refutation not found, incomplete strategy% (25658)------------------------------
% 1.45/0.56  % (25658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (25658)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (25658)Memory used [KB]: 10618
% 1.45/0.56  % (25658)Time elapsed: 0.155 s
% 1.45/0.56  % (25658)------------------------------
% 1.45/0.56  % (25658)------------------------------
% 1.45/0.56  % (25650)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.45/0.56  % (25653)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.45/0.56  % (25650)Refutation not found, incomplete strategy% (25650)------------------------------
% 1.45/0.56  % (25650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (25650)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (25650)Memory used [KB]: 10618
% 1.45/0.56  % (25650)Time elapsed: 0.131 s
% 1.45/0.56  % (25650)------------------------------
% 1.45/0.56  % (25650)------------------------------
% 1.45/0.56  % (25654)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.45/0.57  % (25659)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.64/0.57  % (25640)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.57  % (25659)Refutation not found, incomplete strategy% (25659)------------------------------
% 1.64/0.57  % (25659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (25647)Memory used [KB]: 6524
% 1.64/0.57  % (25647)Time elapsed: 0.145 s
% 1.64/0.57  % (25647)------------------------------
% 1.64/0.57  % (25647)------------------------------
% 1.64/0.57  % (25659)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (25659)Memory used [KB]: 6140
% 1.64/0.57  % (25659)Time elapsed: 0.142 s
% 1.64/0.57  % (25659)------------------------------
% 1.64/0.57  % (25659)------------------------------
% 1.64/0.58  % (25633)Success in time 0.226 s
%------------------------------------------------------------------------------
