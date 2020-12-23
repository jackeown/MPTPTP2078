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
% DateTime   : Thu Dec  3 12:40:50 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 271 expanded)
%              Number of leaves         :   11 (  75 expanded)
%              Depth                    :   20
%              Number of atoms          :  142 ( 546 expanded)
%              Number of equality atoms :   65 ( 317 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7121)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (7116)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (7097)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (7113)Refutation not found, incomplete strategy% (7113)------------------------------
% (7113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7123)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (7113)Termination reason: Refutation not found, incomplete strategy
% (7108)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark

% (7113)Memory used [KB]: 10618
% (7113)Time elapsed: 0.144 s
% (7113)------------------------------
% (7113)------------------------------
% (7104)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (7121)Refutation not found, incomplete strategy% (7121)------------------------------
% (7121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7121)Termination reason: Refutation not found, incomplete strategy

% (7121)Memory used [KB]: 10746
% (7121)Time elapsed: 0.150 s
% (7121)------------------------------
% (7121)------------------------------
% (7107)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f272,plain,(
    $false ),
    inference(subsumption_resolution,[],[f271,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f271,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f270,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f270,plain,(
    ! [X3] : sK0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(subsumption_resolution,[],[f269,f172])).

fof(f172,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f167,f50])).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f19,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f167,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(factoring,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(sK1,sK1,sK1,sK1)))
      | ~ r2_hidden(X0,k4_xboole_0(sK0,X2)) ) ),
    inference(resolution,[],[f101,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f101,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(sK1,sK1,sK1,sK1))) ) ),
    inference(subsumption_resolution,[],[f78,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(sK1,sK1,sK1,sK1))) ) ),
    inference(forward_demodulation,[],[f97,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(sK1,sK1,sK1,sK1)))
      | ~ r2_hidden(X0,k4_xboole_0(X2,k1_xboole_0)) ) ),
    inference(resolution,[],[f78,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f78,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(sK1,sK1,sK1,sK1))) ) ),
    inference(resolution,[],[f70,f68])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
      | r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f67,f50])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f269,plain,(
    ! [X3] :
      ( r2_hidden(sK1,k1_xboole_0)
      | sK0 = k4_xboole_0(k1_xboole_0,X3) ) ),
    inference(subsumption_resolution,[],[f265,f85])).

fof(f85,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f76,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f29,f47])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f76,plain,(
    ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f73,f49])).

fof(f49,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f21,f48])).

fof(f21,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f72,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f72,plain,(
    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f26,f50])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f265,plain,(
    ! [X3] :
      ( r2_hidden(sK1,sK0)
      | r2_hidden(sK1,k1_xboole_0)
      | sK0 = k4_xboole_0(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f41,f226])).

fof(f226,plain,(
    ! [X16] : sK1 = sK3(k1_xboole_0,X16,sK0) ),
    inference(subsumption_resolution,[],[f225,f20])).

fof(f225,plain,(
    ! [X16] :
      ( k1_xboole_0 = sK0
      | sK1 = sK3(k1_xboole_0,X16,sK0) ) ),
    inference(forward_demodulation,[],[f213,f23])).

fof(f213,plain,(
    ! [X16] :
      ( sK1 = sK3(k1_xboole_0,X16,sK0)
      | sK0 = k4_xboole_0(k1_xboole_0,X16) ) ),
    inference(resolution,[],[f95,f172])).

fof(f95,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK3(X6,X7,sK0),X6)
      | sK1 = sK3(X6,X7,sK0)
      | sK0 = k4_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f90,f41])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f81,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,X1)
      | sK1 = X0 ) ),
    inference(forward_demodulation,[],[f86,f22])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 = X0
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f81,f68])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,sK0)
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,sK0)
      | sK1 = X0
      | sK1 = X0 ) ),
    inference(resolution,[],[f70,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:48:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.16/0.51  % (7101)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.16/0.52  % (7099)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.16/0.52  % (7106)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.53  % (7103)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.53  % (7105)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.53  % (7109)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.53  % (7109)Refutation not found, incomplete strategy% (7109)------------------------------
% 1.32/0.53  % (7109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (7109)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (7109)Memory used [KB]: 10618
% 1.32/0.53  % (7109)Time elapsed: 0.134 s
% 1.32/0.53  % (7109)------------------------------
% 1.32/0.53  % (7109)------------------------------
% 1.32/0.54  % (7126)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.54  % (7126)Refutation not found, incomplete strategy% (7126)------------------------------
% 1.32/0.54  % (7126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (7126)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (7126)Memory used [KB]: 1663
% 1.32/0.54  % (7126)Time elapsed: 0.002 s
% 1.32/0.54  % (7126)------------------------------
% 1.32/0.54  % (7126)------------------------------
% 1.32/0.54  % (7122)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.54  % (7118)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.54  % (7098)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.54  % (7125)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.54  % (7098)Refutation not found, incomplete strategy% (7098)------------------------------
% 1.32/0.54  % (7098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (7098)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (7098)Memory used [KB]: 1663
% 1.32/0.54  % (7098)Time elapsed: 0.127 s
% 1.32/0.54  % (7098)------------------------------
% 1.32/0.54  % (7098)------------------------------
% 1.32/0.54  % (7110)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.32/0.54  % (7100)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.54  % (7102)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.54  % (7117)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.54  % (7120)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.54  % (7124)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.55  % (7115)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.55  % (7112)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.55  % (7114)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.32/0.55  % (7113)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.32/0.55  % (7124)Refutation found. Thanks to Tanya!
% 1.32/0.55  % SZS status Theorem for theBenchmark
% 1.32/0.55  % SZS output start Proof for theBenchmark
% 1.32/0.55  % (7121)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.55  % (7116)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.55  % (7097)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.32/0.55  % (7113)Refutation not found, incomplete strategy% (7113)------------------------------
% 1.32/0.55  % (7113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (7123)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.55  % (7113)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  % (7108)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.55  
% 1.32/0.55  % (7113)Memory used [KB]: 10618
% 1.32/0.55  % (7113)Time elapsed: 0.144 s
% 1.32/0.55  % (7113)------------------------------
% 1.32/0.55  % (7113)------------------------------
% 1.32/0.55  % (7104)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.56  % (7121)Refutation not found, incomplete strategy% (7121)------------------------------
% 1.32/0.56  % (7121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (7121)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (7121)Memory used [KB]: 10746
% 1.32/0.56  % (7121)Time elapsed: 0.150 s
% 1.32/0.56  % (7121)------------------------------
% 1.32/0.56  % (7121)------------------------------
% 1.32/0.56  % (7107)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.56  fof(f272,plain,(
% 1.32/0.56    $false),
% 1.32/0.56    inference(subsumption_resolution,[],[f271,f20])).
% 1.32/0.56  fof(f20,plain,(
% 1.32/0.56    k1_xboole_0 != sK0),
% 1.32/0.56    inference(cnf_transformation,[],[f18])).
% 1.32/0.56  fof(f18,plain,(
% 1.32/0.56    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.32/0.56    inference(ennf_transformation,[],[f17])).
% 1.32/0.56  fof(f17,negated_conjecture,(
% 1.32/0.56    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.32/0.56    inference(negated_conjecture,[],[f16])).
% 1.32/0.56  fof(f16,conjecture,(
% 1.32/0.56    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 1.32/0.56  fof(f271,plain,(
% 1.32/0.56    k1_xboole_0 = sK0),
% 1.32/0.56    inference(forward_demodulation,[],[f270,f23])).
% 1.32/0.56  fof(f23,plain,(
% 1.32/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f8])).
% 1.32/0.56  fof(f8,axiom,(
% 1.32/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.32/0.56  fof(f270,plain,(
% 1.32/0.56    ( ! [X3] : (sK0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f269,f172])).
% 1.32/0.56  fof(f172,plain,(
% 1.32/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.56    inference(forward_demodulation,[],[f167,f50])).
% 1.32/0.56  fof(f50,plain,(
% 1.32/0.56    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.56    inference(definition_unfolding,[],[f19,f48])).
% 1.32/0.56  fof(f48,plain,(
% 1.32/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f24,f47])).
% 1.32/0.56  fof(f47,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f36,f46])).
% 1.32/0.56  fof(f46,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f13])).
% 1.32/0.56  fof(f13,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.56  fof(f36,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f12])).
% 1.32/0.56  fof(f12,axiom,(
% 1.32/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.56  fof(f24,plain,(
% 1.32/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f11])).
% 1.32/0.56  fof(f11,axiom,(
% 1.32/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.56  fof(f19,plain,(
% 1.32/0.56    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.32/0.56    inference(cnf_transformation,[],[f18])).
% 1.32/0.56  fof(f167,plain,(
% 1.32/0.56    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) )),
% 1.32/0.56    inference(factoring,[],[f102])).
% 1.32/0.56  fof(f102,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(sK1,sK1,sK1,sK1))) | ~r2_hidden(X0,k4_xboole_0(sK0,X2))) )),
% 1.32/0.56    inference(resolution,[],[f101,f69])).
% 1.32/0.56  fof(f69,plain,(
% 1.32/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.32/0.56    inference(equality_resolution,[],[f43])).
% 1.32/0.56  fof(f43,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.32/0.56    inference(cnf_transformation,[],[f1])).
% 1.32/0.56  fof(f1,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.32/0.56  fof(f101,plain,(
% 1.32/0.56    ( ! [X2,X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(sK1,sK1,sK1,sK1)))) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f78,f100])).
% 1.32/0.56  fof(f100,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(sK1,sK1,sK1,sK1)))) )),
% 1.32/0.56    inference(forward_demodulation,[],[f97,f22])).
% 1.32/0.56  fof(f22,plain,(
% 1.32/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.32/0.56    inference(cnf_transformation,[],[f6])).
% 1.32/0.56  fof(f6,axiom,(
% 1.32/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.32/0.56  fof(f97,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(sK1,sK1,sK1,sK1))) | ~r2_hidden(X0,k4_xboole_0(X2,k1_xboole_0))) )),
% 1.32/0.56    inference(resolution,[],[f78,f68])).
% 1.32/0.56  fof(f68,plain,(
% 1.32/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.32/0.56    inference(equality_resolution,[],[f44])).
% 1.32/0.56  fof(f44,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.32/0.56    inference(cnf_transformation,[],[f1])).
% 1.32/0.56  fof(f78,plain,(
% 1.32/0.56    ( ! [X2,X1] : (r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,sK0) | ~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(sK1,sK1,sK1,sK1)))) )),
% 1.32/0.56    inference(resolution,[],[f70,f68])).
% 1.32/0.56  fof(f70,plain,(
% 1.32/0.56    ( ! [X0] : (r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK0)) )),
% 1.32/0.56    inference(superposition,[],[f67,f50])).
% 1.32/0.56  fof(f67,plain,(
% 1.32/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.32/0.56    inference(equality_resolution,[],[f45])).
% 1.32/0.56  fof(f45,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.32/0.56    inference(cnf_transformation,[],[f1])).
% 1.32/0.56  fof(f269,plain,(
% 1.32/0.56    ( ! [X3] : (r2_hidden(sK1,k1_xboole_0) | sK0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f265,f85])).
% 1.32/0.56  fof(f85,plain,(
% 1.32/0.56    ~r2_hidden(sK1,sK0)),
% 1.32/0.56    inference(duplicate_literal_removal,[],[f84])).
% 1.32/0.56  fof(f84,plain,(
% 1.32/0.56    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,sK0)),
% 1.32/0.56    inference(resolution,[],[f76,f51])).
% 1.32/0.56  fof(f51,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f29,f47])).
% 1.32/0.56  fof(f29,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f15])).
% 1.32/0.56  fof(f15,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.32/0.56  fof(f76,plain,(
% 1.32/0.56    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f73,f49])).
% 1.32/0.56  fof(f49,plain,(
% 1.32/0.56    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.32/0.56    inference(definition_unfolding,[],[f21,f48])).
% 1.32/0.56  fof(f21,plain,(
% 1.32/0.56    sK0 != k1_tarski(sK1)),
% 1.32/0.56    inference(cnf_transformation,[],[f18])).
% 1.32/0.56  fof(f73,plain,(
% 1.32/0.56    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.32/0.56    inference(resolution,[],[f72,f39])).
% 1.32/0.56  fof(f39,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.32/0.56    inference(cnf_transformation,[],[f2])).
% 1.32/0.56  fof(f2,axiom,(
% 1.32/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.56  fof(f72,plain,(
% 1.32/0.56    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.56    inference(trivial_inequality_removal,[],[f71])).
% 1.32/0.56  fof(f71,plain,(
% 1.32/0.56    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.56    inference(superposition,[],[f26,f50])).
% 1.32/0.56  fof(f26,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f3])).
% 1.32/0.56  fof(f3,axiom,(
% 1.32/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.32/0.56  fof(f265,plain,(
% 1.32/0.56    ( ! [X3] : (r2_hidden(sK1,sK0) | r2_hidden(sK1,k1_xboole_0) | sK0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.32/0.56    inference(superposition,[],[f41,f226])).
% 1.32/0.56  fof(f226,plain,(
% 1.32/0.56    ( ! [X16] : (sK1 = sK3(k1_xboole_0,X16,sK0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f225,f20])).
% 1.32/0.56  fof(f225,plain,(
% 1.32/0.56    ( ! [X16] : (k1_xboole_0 = sK0 | sK1 = sK3(k1_xboole_0,X16,sK0)) )),
% 1.32/0.56    inference(forward_demodulation,[],[f213,f23])).
% 1.32/0.56  fof(f213,plain,(
% 1.32/0.56    ( ! [X16] : (sK1 = sK3(k1_xboole_0,X16,sK0) | sK0 = k4_xboole_0(k1_xboole_0,X16)) )),
% 1.32/0.56    inference(resolution,[],[f95,f172])).
% 1.32/0.56  fof(f95,plain,(
% 1.32/0.56    ( ! [X6,X7] : (r2_hidden(sK3(X6,X7,sK0),X6) | sK1 = sK3(X6,X7,sK0) | sK0 = k4_xboole_0(X6,X7)) )),
% 1.32/0.56    inference(resolution,[],[f90,f41])).
% 1.32/0.56  fof(f90,plain,(
% 1.32/0.56    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = X0) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f81,f89])).
% 1.32/0.56  fof(f89,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,X1) | sK1 = X0) )),
% 1.32/0.56    inference(forward_demodulation,[],[f86,f22])).
% 1.32/0.56  fof(f86,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | sK1 = X0 | ~r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.32/0.56    inference(resolution,[],[f81,f68])).
% 1.32/0.56  fof(f81,plain,(
% 1.32/0.56    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK0) | sK1 = X0) )),
% 1.32/0.56    inference(duplicate_literal_removal,[],[f77])).
% 1.32/0.56  fof(f77,plain,(
% 1.32/0.56    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK0) | sK1 = X0 | sK1 = X0) )),
% 1.32/0.56    inference(resolution,[],[f70,f64])).
% 1.32/0.56  fof(f64,plain,(
% 1.32/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.32/0.56    inference(equality_resolution,[],[f56])).
% 1.32/0.56  fof(f56,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.32/0.56    inference(definition_unfolding,[],[f33,f47])).
% 1.32/0.56  fof(f33,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.32/0.56    inference(cnf_transformation,[],[f10])).
% 1.32/0.56  fof(f10,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.32/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.32/0.56  fof(f41,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.32/0.56    inference(cnf_transformation,[],[f1])).
% 1.32/0.56  % SZS output end Proof for theBenchmark
% 1.32/0.56  % (7124)------------------------------
% 1.32/0.56  % (7124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (7124)Termination reason: Refutation
% 1.32/0.56  
% 1.32/0.56  % (7124)Memory used [KB]: 6396
% 1.32/0.56  % (7124)Time elapsed: 0.135 s
% 1.32/0.56  % (7124)------------------------------
% 1.32/0.56  % (7124)------------------------------
% 1.32/0.56  % (7096)Success in time 0.2 s
%------------------------------------------------------------------------------
