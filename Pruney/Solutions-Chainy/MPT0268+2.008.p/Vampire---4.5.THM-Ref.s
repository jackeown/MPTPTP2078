%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:37 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 244 expanded)
%              Number of leaves         :   16 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          :  155 ( 347 expanded)
%              Number of equality atoms :   69 ( 222 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f941,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f92,f867,f940])).

fof(f940,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f931])).

fof(f931,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f90,f81,f911,f97])).

fof(f97,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r2_hidden(X4,X3)
      | ~ r2_hidden(X4,X2) ) ),
    inference(superposition,[],[f74,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
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

fof(f911,plain,
    ( r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f894])).

fof(f894,plain,
    ( sK0 != sK0
    | r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_1 ),
    inference(superposition,[],[f36,f85])).

fof(f85,plain,
    ( sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_1
  <=> sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f90,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f867,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f865])).

fof(f865,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f89,f843,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f843,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f842])).

fof(f842,plain,
    ( sK0 != sK0
    | ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl4_1 ),
    inference(superposition,[],[f86,f784])).

fof(f784,plain,(
    ! [X6,X7] :
      ( k4_xboole_0(X7,X6) = X7
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(forward_demodulation,[],[f783,f306])).

fof(f306,plain,(
    ! [X4] : k5_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(subsumption_resolution,[],[f226,f303])).

fof(f303,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f292,f24])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f292,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_xboole_0,X3)
      | r1_xboole_0(k1_xboole_0,X3) ) ),
    inference(trivial_inequality_removal,[],[f278])).

fof(f278,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X3)
      | ~ r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f36,f268])).

fof(f268,plain,(
    ! [X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f260,f140])).

fof(f140,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f135,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f135,plain,(
    ! [X5] : k5_xboole_0(X5,k4_xboole_0(X5,X5)) = X5 ),
    inference(superposition,[],[f56,f25])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f260,plain,(
    ! [X1] :
      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X1)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f182,f175])).

fof(f175,plain,(
    ! [X3] :
      ( k1_xboole_0 = k4_xboole_0(X3,X3)
      | ~ r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f145,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f145,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9)) = k4_xboole_0(X9,X9) ),
    inference(superposition,[],[f59,f25])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f29,f29])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f182,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2)) ),
    inference(superposition,[],[f56,f145])).

fof(f226,plain,(
    ! [X4] :
      ( k5_xboole_0(X4,k1_xboole_0) = X4
      | ~ r1_xboole_0(k1_xboole_0,X4) ) ),
    inference(superposition,[],[f135,f200])).

fof(f200,plain,(
    ! [X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X1)
      | ~ r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f171,f25])).

fof(f171,plain,(
    ! [X1] :
      ( k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f145,f37])).

fof(f783,plain,(
    ! [X6,X7] :
      ( k4_xboole_0(X7,X6) = k5_xboole_0(X7,k1_xboole_0)
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(forward_demodulation,[],[f755,f307])).

fof(f307,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(subsumption_resolution,[],[f200,f303])).

fof(f755,plain,(
    ! [X6,X7] :
      ( k4_xboole_0(X7,X6) = k5_xboole_0(X7,k4_xboole_0(X6,X6))
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(superposition,[],[f152,f37])).

fof(f152,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f56,f59])).

fof(f86,plain,
    ( sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f89,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f92,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f58,f88,f84])).

fof(f58,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f22,f55])).

fof(f22,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f91,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f57,f88,f84])).

fof(f57,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f23,f55])).

fof(f23,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:47:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (16178)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.49  % (16194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (16194)Refutation not found, incomplete strategy% (16194)------------------------------
% 0.20/0.51  % (16194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.51  % (16194)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.51  
% 1.14/0.51  % (16194)Memory used [KB]: 10618
% 1.14/0.51  % (16194)Time elapsed: 0.091 s
% 1.14/0.51  % (16194)------------------------------
% 1.14/0.51  % (16194)------------------------------
% 1.14/0.52  % (16182)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.14/0.54  % (16183)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.14/0.54  % (16179)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.14/0.54  % (16181)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.14/0.54  % (16179)Refutation not found, incomplete strategy% (16179)------------------------------
% 1.14/0.54  % (16179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.54  % (16179)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.54  
% 1.14/0.54  % (16179)Memory used [KB]: 1663
% 1.14/0.54  % (16179)Time elapsed: 0.123 s
% 1.14/0.54  % (16179)------------------------------
% 1.14/0.54  % (16179)------------------------------
% 1.14/0.54  % (16193)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.54  % (16198)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.37/0.54  % (16185)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.37/0.54  % (16203)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.55  % (16207)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.55  % (16207)Refutation not found, incomplete strategy% (16207)------------------------------
% 1.37/0.55  % (16207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (16207)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (16207)Memory used [KB]: 1663
% 1.37/0.55  % (16207)Time elapsed: 0.001 s
% 1.37/0.55  % (16207)------------------------------
% 1.37/0.55  % (16207)------------------------------
% 1.37/0.55  % (16200)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.37/0.55  % (16202)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.55  % (16205)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.55  % (16195)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.37/0.55  % (16195)Refutation not found, incomplete strategy% (16195)------------------------------
% 1.37/0.55  % (16195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (16195)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (16195)Memory used [KB]: 1663
% 1.37/0.55  % (16195)Time elapsed: 0.137 s
% 1.37/0.55  % (16195)------------------------------
% 1.37/0.55  % (16195)------------------------------
% 1.37/0.55  % (16206)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.55  % (16187)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.55  % (16199)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.55  % (16197)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.55  % (16191)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.37/0.55  % (16186)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.37/0.55  % (16206)Refutation not found, incomplete strategy% (16206)------------------------------
% 1.37/0.55  % (16206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (16206)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (16206)Memory used [KB]: 10746
% 1.37/0.55  % (16206)Time elapsed: 0.149 s
% 1.37/0.55  % (16206)------------------------------
% 1.37/0.55  % (16206)------------------------------
% 1.37/0.56  % (16190)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.56  % (16184)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.56  % (16189)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.56  % (16201)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.37/0.56  % (16189)Refutation not found, incomplete strategy% (16189)------------------------------
% 1.37/0.56  % (16189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (16189)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (16189)Memory used [KB]: 6140
% 1.37/0.56  % (16189)Time elapsed: 0.148 s
% 1.37/0.56  % (16189)------------------------------
% 1.37/0.56  % (16189)------------------------------
% 1.37/0.56  % (16192)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.37/0.56  % (16192)Refutation not found, incomplete strategy% (16192)------------------------------
% 1.37/0.56  % (16192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (16192)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (16192)Memory used [KB]: 1663
% 1.37/0.56  % (16192)Time elapsed: 0.113 s
% 1.37/0.56  % (16192)------------------------------
% 1.37/0.56  % (16192)------------------------------
% 1.37/0.61  % (16258)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.37/0.61  % (16191)Refutation found. Thanks to Tanya!
% 1.37/0.61  % SZS status Theorem for theBenchmark
% 1.37/0.61  % SZS output start Proof for theBenchmark
% 1.37/0.61  fof(f941,plain,(
% 1.37/0.61    $false),
% 1.37/0.61    inference(avatar_sat_refutation,[],[f91,f92,f867,f940])).
% 1.37/0.61  fof(f940,plain,(
% 1.37/0.61    ~spl4_1 | ~spl4_2),
% 1.37/0.61    inference(avatar_contradiction_clause,[],[f931])).
% 1.37/0.61  fof(f931,plain,(
% 1.37/0.61    $false | (~spl4_1 | ~spl4_2)),
% 1.37/0.61    inference(unit_resulting_resolution,[],[f90,f81,f911,f97])).
% 1.37/0.61  fof(f97,plain,(
% 1.37/0.61    ( ! [X4,X2,X3] : (~r1_xboole_0(X2,X3) | ~r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) )),
% 1.37/0.61    inference(superposition,[],[f74,f37])).
% 1.37/0.61  fof(f37,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f10])).
% 1.37/0.61  fof(f10,axiom,(
% 1.37/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.37/0.61  fof(f74,plain,(
% 1.37/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.37/0.61    inference(equality_resolution,[],[f44])).
% 1.37/0.61  fof(f44,plain,(
% 1.37/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.37/0.61    inference(cnf_transformation,[],[f2])).
% 1.37/0.61  fof(f2,axiom,(
% 1.37/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.37/0.61  fof(f911,plain,(
% 1.37/0.61    r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_1),
% 1.37/0.61    inference(trivial_inequality_removal,[],[f894])).
% 1.37/0.61  fof(f894,plain,(
% 1.37/0.61    sK0 != sK0 | r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_1),
% 1.37/0.61    inference(superposition,[],[f36,f85])).
% 1.37/0.61  fof(f85,plain,(
% 1.37/0.61    sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_1),
% 1.37/0.61    inference(avatar_component_clause,[],[f84])).
% 1.37/0.61  fof(f84,plain,(
% 1.37/0.61    spl4_1 <=> sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.37/0.61  fof(f36,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f10])).
% 1.37/0.61  fof(f81,plain,(
% 1.37/0.61    ( ! [X4,X2,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X1,X2))) )),
% 1.37/0.61    inference(equality_resolution,[],[f80])).
% 1.37/0.61  fof(f80,plain,(
% 1.37/0.61    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X4,X4,X1,X2) != X3) )),
% 1.37/0.61    inference(equality_resolution,[],[f65])).
% 1.37/0.61  fof(f65,plain,(
% 1.37/0.61    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.37/0.61    inference(definition_unfolding,[],[f51,f38])).
% 1.37/0.61  fof(f38,plain,(
% 1.37/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f14])).
% 1.37/0.61  fof(f14,axiom,(
% 1.37/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.37/0.61  fof(f51,plain,(
% 1.37/0.61    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.37/0.61    inference(cnf_transformation,[],[f21])).
% 1.37/0.61  fof(f21,plain,(
% 1.37/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.37/0.61    inference(ennf_transformation,[],[f11])).
% 1.37/0.61  fof(f11,axiom,(
% 1.37/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.37/0.61  fof(f90,plain,(
% 1.37/0.61    r2_hidden(sK1,sK0) | ~spl4_2),
% 1.37/0.61    inference(avatar_component_clause,[],[f88])).
% 1.37/0.61  fof(f88,plain,(
% 1.37/0.61    spl4_2 <=> r2_hidden(sK1,sK0)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.37/0.61  fof(f867,plain,(
% 1.37/0.61    spl4_1 | spl4_2),
% 1.37/0.61    inference(avatar_contradiction_clause,[],[f865])).
% 1.37/0.61  fof(f865,plain,(
% 1.37/0.61    $false | (spl4_1 | spl4_2)),
% 1.37/0.61    inference(unit_resulting_resolution,[],[f89,f843,f60])).
% 1.37/0.61  fof(f60,plain,(
% 1.37/0.61    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.37/0.61    inference(definition_unfolding,[],[f31,f55])).
% 1.37/0.61  fof(f55,plain,(
% 1.37/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.37/0.61    inference(definition_unfolding,[],[f26,f54])).
% 1.37/0.61  fof(f54,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.37/0.61    inference(definition_unfolding,[],[f28,f38])).
% 1.37/0.61  fof(f28,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f13])).
% 1.37/0.61  fof(f13,axiom,(
% 1.37/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.37/0.61  fof(f26,plain,(
% 1.37/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f12])).
% 1.37/0.61  fof(f12,axiom,(
% 1.37/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.37/0.61  fof(f31,plain,(
% 1.37/0.61    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f19])).
% 1.37/0.61  fof(f19,plain,(
% 1.37/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.37/0.61    inference(ennf_transformation,[],[f15])).
% 1.37/0.61  fof(f15,axiom,(
% 1.37/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.37/0.61  fof(f843,plain,(
% 1.37/0.61    ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | spl4_1),
% 1.37/0.61    inference(trivial_inequality_removal,[],[f842])).
% 1.37/0.61  fof(f842,plain,(
% 1.37/0.61    sK0 != sK0 | ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | spl4_1),
% 1.37/0.61    inference(superposition,[],[f86,f784])).
% 1.37/0.61  fof(f784,plain,(
% 1.37/0.61    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = X7 | ~r1_xboole_0(X6,X7)) )),
% 1.37/0.61    inference(forward_demodulation,[],[f783,f306])).
% 1.37/0.61  fof(f306,plain,(
% 1.37/0.61    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = X4) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f226,f303])).
% 1.37/0.61  fof(f303,plain,(
% 1.37/0.61    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.37/0.61    inference(resolution,[],[f292,f24])).
% 1.37/0.61  fof(f24,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f6])).
% 1.37/0.61  fof(f6,axiom,(
% 1.37/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.37/0.61  fof(f292,plain,(
% 1.37/0.61    ( ! [X3] : (~r1_tarski(k1_xboole_0,X3) | r1_xboole_0(k1_xboole_0,X3)) )),
% 1.37/0.61    inference(trivial_inequality_removal,[],[f278])).
% 1.37/0.61  fof(f278,plain,(
% 1.37/0.61    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X3) | ~r1_tarski(k1_xboole_0,X3)) )),
% 1.37/0.61    inference(superposition,[],[f36,f268])).
% 1.37/0.61  fof(f268,plain,(
% 1.37/0.61    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) | ~r1_tarski(k1_xboole_0,X1)) )),
% 1.37/0.61    inference(forward_demodulation,[],[f260,f140])).
% 1.37/0.61  fof(f140,plain,(
% 1.37/0.61    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.37/0.61    inference(superposition,[],[f135,f25])).
% 1.37/0.61  fof(f25,plain,(
% 1.37/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.37/0.61    inference(cnf_transformation,[],[f7])).
% 1.37/0.61  fof(f7,axiom,(
% 1.37/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.37/0.61  fof(f135,plain,(
% 1.37/0.61    ( ! [X5] : (k5_xboole_0(X5,k4_xboole_0(X5,X5)) = X5) )),
% 1.37/0.61    inference(superposition,[],[f56,f25])).
% 1.37/0.61  fof(f56,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.37/0.61    inference(definition_unfolding,[],[f30,f29])).
% 1.37/0.61  fof(f29,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f8])).
% 1.37/0.61  fof(f8,axiom,(
% 1.37/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.37/0.61  fof(f30,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.37/0.61    inference(cnf_transformation,[],[f4])).
% 1.37/0.61  fof(f4,axiom,(
% 1.37/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.37/0.61  fof(f260,plain,(
% 1.37/0.61    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X1) | ~r1_tarski(k1_xboole_0,X1)) )),
% 1.37/0.61    inference(superposition,[],[f182,f175])).
% 1.37/0.61  fof(f175,plain,(
% 1.37/0.61    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | ~r1_tarski(k1_xboole_0,X3)) )),
% 1.37/0.61    inference(superposition,[],[f145,f61])).
% 1.37/0.61  fof(f61,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.37/0.61    inference(definition_unfolding,[],[f32,f29])).
% 1.37/0.61  fof(f32,plain,(
% 1.37/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.37/0.61    inference(cnf_transformation,[],[f20])).
% 1.37/0.61  fof(f20,plain,(
% 1.37/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.37/0.61    inference(ennf_transformation,[],[f5])).
% 1.37/0.61  fof(f5,axiom,(
% 1.37/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.37/0.61  fof(f145,plain,(
% 1.37/0.61    ( ! [X9] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9)) = k4_xboole_0(X9,X9)) )),
% 1.37/0.61    inference(superposition,[],[f59,f25])).
% 1.37/0.61  fof(f59,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.37/0.61    inference(definition_unfolding,[],[f27,f29,f29])).
% 1.37/0.61  fof(f27,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f1])).
% 1.37/0.61  fof(f1,axiom,(
% 1.37/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.37/0.61  fof(f182,plain,(
% 1.37/0.61    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2))) )),
% 1.37/0.61    inference(superposition,[],[f56,f145])).
% 1.37/0.61  fof(f226,plain,(
% 1.37/0.61    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = X4 | ~r1_xboole_0(k1_xboole_0,X4)) )),
% 1.37/0.61    inference(superposition,[],[f135,f200])).
% 1.37/0.61  fof(f200,plain,(
% 1.37/0.61    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1) | ~r1_xboole_0(k1_xboole_0,X1)) )),
% 1.37/0.61    inference(forward_demodulation,[],[f171,f25])).
% 1.37/0.61  fof(f171,plain,(
% 1.37/0.61    ( ! [X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X1)) )),
% 1.37/0.61    inference(superposition,[],[f145,f37])).
% 1.37/0.61  fof(f783,plain,(
% 1.37/0.61    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k5_xboole_0(X7,k1_xboole_0) | ~r1_xboole_0(X6,X7)) )),
% 1.37/0.61    inference(forward_demodulation,[],[f755,f307])).
% 1.37/0.61  fof(f307,plain,(
% 1.37/0.61    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f200,f303])).
% 1.37/0.61  fof(f755,plain,(
% 1.37/0.61    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k5_xboole_0(X7,k4_xboole_0(X6,X6)) | ~r1_xboole_0(X6,X7)) )),
% 1.37/0.61    inference(superposition,[],[f152,f37])).
% 1.37/0.61  fof(f152,plain,(
% 1.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.37/0.61    inference(superposition,[],[f56,f59])).
% 1.37/0.61  fof(f86,plain,(
% 1.37/0.61    sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_1),
% 1.37/0.61    inference(avatar_component_clause,[],[f84])).
% 1.37/0.61  fof(f89,plain,(
% 1.37/0.61    ~r2_hidden(sK1,sK0) | spl4_2),
% 1.37/0.61    inference(avatar_component_clause,[],[f88])).
% 1.37/0.61  fof(f92,plain,(
% 1.37/0.61    spl4_1 | ~spl4_2),
% 1.37/0.61    inference(avatar_split_clause,[],[f58,f88,f84])).
% 1.37/0.61  fof(f58,plain,(
% 1.37/0.61    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.37/0.61    inference(definition_unfolding,[],[f22,f55])).
% 1.37/0.61  fof(f22,plain,(
% 1.37/0.61    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.37/0.61    inference(cnf_transformation,[],[f18])).
% 1.37/0.61  fof(f18,plain,(
% 1.37/0.61    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.37/0.61    inference(ennf_transformation,[],[f17])).
% 1.37/0.61  fof(f17,negated_conjecture,(
% 1.37/0.61    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.37/0.61    inference(negated_conjecture,[],[f16])).
% 1.37/0.61  fof(f16,conjecture,(
% 1.37/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.37/0.61  fof(f91,plain,(
% 1.37/0.61    ~spl4_1 | spl4_2),
% 1.37/0.61    inference(avatar_split_clause,[],[f57,f88,f84])).
% 1.37/0.61  fof(f57,plain,(
% 1.37/0.61    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.37/0.61    inference(definition_unfolding,[],[f23,f55])).
% 1.37/0.61  fof(f23,plain,(
% 1.37/0.61    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.37/0.61    inference(cnf_transformation,[],[f18])).
% 1.37/0.61  % SZS output end Proof for theBenchmark
% 1.37/0.61  % (16191)------------------------------
% 1.37/0.61  % (16191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.61  % (16191)Termination reason: Refutation
% 1.37/0.61  
% 1.37/0.61  % (16191)Memory used [KB]: 6652
% 1.37/0.61  % (16191)Time elapsed: 0.200 s
% 1.37/0.61  % (16191)------------------------------
% 1.37/0.61  % (16191)------------------------------
% 1.37/0.61  % (16177)Success in time 0.243 s
%------------------------------------------------------------------------------
