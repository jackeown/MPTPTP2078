%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:28 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 648 expanded)
%              Number of leaves         :   12 ( 209 expanded)
%              Depth                    :   22
%              Number of atoms          :   73 ( 660 expanded)
%              Number of equality atoms :   62 ( 649 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(subsumption_resolution,[],[f281,f51])).

fof(f51,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_enumset1(X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f281,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f279])).

fof(f279,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f42,f274])).

fof(f274,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f251,f226])).

fof(f226,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f220,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f220,plain,(
    k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f204,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f204,plain,(
    ! [X0] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = X0 ),
    inference(backward_demodulation,[],[f55,f200])).

fof(f200,plain,(
    ! [X5] : k5_xboole_0(k1_xboole_0,X5) = X5 ),
    inference(forward_demodulation,[],[f193,f26])).

fof(f193,plain,(
    ! [X5] : k5_xboole_0(X5,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f162,f29])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f162,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X8)) ),
    inference(forward_demodulation,[],[f147,f128])).

fof(f128,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[],[f109,f29])).

fof(f109,plain,(
    ! [X8] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X8,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f96,f26])).

fof(f96,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X8,k1_xboole_0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X8,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f71,f62])).

fof(f62,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f56,f26])).

fof(f56,plain,(
    k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f55,f27])).

fof(f71,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(superposition,[],[f57,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f55,f29])).

fof(f147,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X8)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X8)) ),
    inference(superposition,[],[f78,f67])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0) ),
    inference(superposition,[],[f28,f62])).

fof(f78,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X3))) ),
    inference(forward_demodulation,[],[f77,f28])).

fof(f77,plain,(
    ! [X2,X3] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X3))) ),
    inference(forward_demodulation,[],[f74,f28])).

fof(f74,plain,(
    ! [X2,X3] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(X2,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X3)) ),
    inference(superposition,[],[f28,f57])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f28,f40])).

fof(f40,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f20,f22,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f251,plain,(
    ! [X2] : k4_xboole_0(X2,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k4_xboole_0(X2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f250,f201])).

fof(f201,plain,(
    ! [X0] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = X0 ),
    inference(backward_demodulation,[],[f128,f200])).

fof(f250,plain,(
    ! [X2] : k4_xboole_0(k4_xboole_0(X2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(X2,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f223,f226])).

fof(f223,plain,(
    ! [X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(X2,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(superposition,[],[f204,f41])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f21,f22,f22])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f39,f39])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (14338)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.51  % (14354)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (14342)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (14331)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (14346)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (14350)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (14334)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (14354)Refutation not found, incomplete strategy% (14354)------------------------------
% 0.22/0.53  % (14354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14346)Refutation not found, incomplete strategy% (14346)------------------------------
% 0.22/0.53  % (14346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14354)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14354)Memory used [KB]: 6140
% 0.22/0.53  % (14354)Time elapsed: 0.115 s
% 0.22/0.53  % (14354)------------------------------
% 0.22/0.53  % (14354)------------------------------
% 0.22/0.53  % (14346)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14346)Memory used [KB]: 1663
% 0.22/0.53  % (14346)Time elapsed: 0.116 s
% 0.22/0.53  % (14346)------------------------------
% 0.22/0.53  % (14346)------------------------------
% 0.22/0.53  % (14342)Refutation not found, incomplete strategy% (14342)------------------------------
% 0.22/0.53  % (14342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14342)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14342)Memory used [KB]: 1663
% 0.22/0.53  % (14342)Time elapsed: 0.112 s
% 0.22/0.53  % (14342)------------------------------
% 0.22/0.53  % (14342)------------------------------
% 0.22/0.53  % (14357)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (14357)Refutation not found, incomplete strategy% (14357)------------------------------
% 0.22/0.53  % (14357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14357)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14357)Memory used [KB]: 1663
% 0.22/0.53  % (14357)Time elapsed: 0.001 s
% 0.22/0.53  % (14357)------------------------------
% 0.22/0.53  % (14357)------------------------------
% 0.22/0.53  % (14329)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (14349)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (14339)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (14330)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (14332)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (14328)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (14352)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (14341)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.48/0.54  % (14355)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.48/0.54  % (14353)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.54  % (14335)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.55  % (14344)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.55  % (14356)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.48/0.55  % (14344)Refutation not found, incomplete strategy% (14344)------------------------------
% 1.48/0.55  % (14344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (14344)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (14344)Memory used [KB]: 10618
% 1.48/0.55  % (14344)Time elapsed: 0.137 s
% 1.48/0.55  % (14344)------------------------------
% 1.48/0.55  % (14344)------------------------------
% 1.48/0.55  % (14336)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.48/0.55  % (14345)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.55  % (14347)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.55  % (14333)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.48/0.55  % (14348)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.55  % (14351)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.48/0.56  % (14337)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.48/0.56  % (14340)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.48/0.56  % (14343)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.56  % (14340)Refutation not found, incomplete strategy% (14340)------------------------------
% 1.48/0.56  % (14340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (14340)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (14340)Memory used [KB]: 10618
% 1.48/0.56  % (14340)Time elapsed: 0.149 s
% 1.48/0.56  % (14340)------------------------------
% 1.48/0.56  % (14340)------------------------------
% 1.56/0.57  % (14355)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f282,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(subsumption_resolution,[],[f281,f51])).
% 1.56/0.57  fof(f51,plain,(
% 1.56/0.57    ( ! [X0,X3] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X3))) )),
% 1.56/0.57    inference(equality_resolution,[],[f50])).
% 1.56/0.57  fof(f50,plain,(
% 1.56/0.57    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X3) != X2) )),
% 1.56/0.57    inference(equality_resolution,[],[f44])).
% 1.56/0.57  fof(f44,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.56/0.57    inference(definition_unfolding,[],[f35,f38])).
% 1.56/0.57  fof(f38,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f36,f37])).
% 1.56/0.57  fof(f37,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f14])).
% 1.56/0.57  fof(f14,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.57  fof(f36,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f13])).
% 1.56/0.57  fof(f13,axiom,(
% 1.56/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.57  fof(f35,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.56/0.57    inference(cnf_transformation,[],[f11])).
% 1.56/0.57  fof(f11,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.56/0.57  fof(f281,plain,(
% 1.56/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f279])).
% 1.56/0.57  fof(f279,plain,(
% 1.56/0.57    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.56/0.57    inference(superposition,[],[f42,f274])).
% 1.56/0.57  fof(f274,plain,(
% 1.56/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.56/0.57    inference(superposition,[],[f251,f226])).
% 1.56/0.57  fof(f226,plain,(
% 1.56/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.56/0.57    inference(forward_demodulation,[],[f220,f26])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.56/0.57  fof(f220,plain,(
% 1.56/0.57    k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.56/0.57    inference(superposition,[],[f204,f27])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f9])).
% 1.56/0.57  fof(f9,axiom,(
% 1.56/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.56/0.57  fof(f204,plain,(
% 1.56/0.57    ( ! [X0] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = X0) )),
% 1.56/0.57    inference(backward_demodulation,[],[f55,f200])).
% 1.56/0.57  fof(f200,plain,(
% 1.56/0.57    ( ! [X5] : (k5_xboole_0(k1_xboole_0,X5) = X5) )),
% 1.56/0.57    inference(forward_demodulation,[],[f193,f26])).
% 1.56/0.57  fof(f193,plain,(
% 1.56/0.57    ( ! [X5] : (k5_xboole_0(X5,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,k1_xboole_0))) )),
% 1.56/0.57    inference(superposition,[],[f162,f29])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.56/0.57  fof(f162,plain,(
% 1.56/0.57    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X8))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f147,f128])).
% 1.56/0.57  fof(f128,plain,(
% 1.56/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0))) )),
% 1.56/0.57    inference(superposition,[],[f109,f29])).
% 1.56/0.57  fof(f109,plain,(
% 1.56/0.57    ( ! [X8] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X8,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,X8)) )),
% 1.56/0.57    inference(forward_demodulation,[],[f96,f26])).
% 1.56/0.57  fof(f96,plain,(
% 1.56/0.57    ( ! [X8] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X8,k1_xboole_0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X8,k2_enumset1(sK0,sK0,sK0,sK0)))) )),
% 1.56/0.57    inference(superposition,[],[f71,f62])).
% 1.56/0.57  fof(f62,plain,(
% 1.56/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.56/0.57    inference(forward_demodulation,[],[f56,f26])).
% 1.56/0.57  fof(f56,plain,(
% 1.56/0.57    k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.56/0.57    inference(superposition,[],[f55,f27])).
% 1.56/0.57  fof(f71,plain,(
% 1.56/0.57    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))) )),
% 1.56/0.57    inference(superposition,[],[f57,f28])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.56/0.57  fof(f57,plain,(
% 1.56/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X0,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) )),
% 1.56/0.57    inference(superposition,[],[f55,f29])).
% 1.56/0.57  fof(f147,plain,(
% 1.56/0.57    ( ! [X8] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X8)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X8))) )),
% 1.56/0.57    inference(superposition,[],[f78,f67])).
% 1.56/0.57  fof(f67,plain,(
% 1.56/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) )),
% 1.56/0.57    inference(superposition,[],[f28,f62])).
% 1.56/0.57  fof(f78,plain,(
% 1.56/0.57    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X3)))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f77,f28])).
% 1.56/0.57  fof(f77,plain,(
% 1.56/0.57    ( ! [X2,X3] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X3)))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f74,f28])).
% 1.56/0.57  fof(f74,plain,(
% 1.56/0.57    ( ! [X2,X3] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(X2,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),X3))) )),
% 1.56/0.57    inference(superposition,[],[f28,f57])).
% 1.56/0.57  fof(f55,plain,(
% 1.56/0.57    ( ! [X0] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.56/0.57    inference(superposition,[],[f28,f40])).
% 1.56/0.57  fof(f40,plain,(
% 1.56/0.57    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.56/0.57    inference(definition_unfolding,[],[f20,f22,f39])).
% 1.56/0.57  fof(f39,plain,(
% 1.56/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f25,f38])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f12])).
% 1.56/0.57  fof(f12,axiom,(
% 1.56/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f10])).
% 1.56/0.57  fof(f10,axiom,(
% 1.56/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.56/0.57  fof(f20,plain,(
% 1.56/0.57    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.56/0.57    inference(cnf_transformation,[],[f19])).
% 1.56/0.57  fof(f19,plain,(
% 1.56/0.57    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.56/0.57    inference(ennf_transformation,[],[f18])).
% 1.56/0.57  fof(f18,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.56/0.57    inference(negated_conjecture,[],[f17])).
% 1.56/0.57  fof(f17,conjecture,(
% 1.56/0.57    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.56/0.57  fof(f251,plain,(
% 1.56/0.57    ( ! [X2] : (k4_xboole_0(X2,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k4_xboole_0(X2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f250,f201])).
% 1.56/0.57  fof(f201,plain,(
% 1.56/0.57    ( ! [X0] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = X0) )),
% 1.56/0.57    inference(backward_demodulation,[],[f128,f200])).
% 1.56/0.57  fof(f250,plain,(
% 1.56/0.57    ( ! [X2] : (k4_xboole_0(k4_xboole_0(X2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(X2,k2_enumset1(sK0,sK0,sK0,sK0))))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f223,f226])).
% 1.56/0.57  fof(f223,plain,(
% 1.56/0.57    ( ! [X2] : (k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(X2,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))) )),
% 1.56/0.57    inference(superposition,[],[f204,f41])).
% 1.56/0.57  fof(f41,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 1.56/0.57    inference(definition_unfolding,[],[f21,f22,f22])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f6])).
% 1.56/0.57  fof(f6,axiom,(
% 1.56/0.57    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.56/0.57  fof(f42,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f24,f39,f39])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f15])).
% 1.56/0.57  fof(f15,axiom,(
% 1.56/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (14355)------------------------------
% 1.56/0.57  % (14355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (14355)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (14355)Memory used [KB]: 6396
% 1.56/0.57  % (14355)Time elapsed: 0.146 s
% 1.56/0.57  % (14355)------------------------------
% 1.56/0.57  % (14355)------------------------------
% 1.56/0.57  % (14327)Success in time 0.207 s
%------------------------------------------------------------------------------
