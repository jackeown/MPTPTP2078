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
% DateTime   : Thu Dec  3 12:36:21 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 130 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 172 expanded)
%              Number of equality atoms :   68 ( 157 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f19])).

fof(f19,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f14])).

% (4386)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (4379)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (4386)Refutation not found, incomplete strategy% (4386)------------------------------
% (4386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4378)Refutation not found, incomplete strategy% (4378)------------------------------
% (4378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4378)Termination reason: Refutation not found, incomplete strategy

% (4378)Memory used [KB]: 6140
% (4378)Time elapsed: 0.110 s
% (4378)------------------------------
% (4378)------------------------------
% (4386)Termination reason: Refutation not found, incomplete strategy

% (4386)Memory used [KB]: 1663
% (4386)Time elapsed: 0.107 s
% (4386)------------------------------
% (4386)------------------------------
% (4377)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (4372)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (4387)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (4372)Refutation not found, incomplete strategy% (4372)------------------------------
% (4372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4372)Termination reason: Refutation not found, incomplete strategy

% (4372)Memory used [KB]: 10618
% (4372)Time elapsed: 0.094 s
% (4372)------------------------------
% (4372)------------------------------
% (4385)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (4365)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f127,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f122,f68])).

fof(f68,plain,(
    ! [X4,X5,X3] : r2_hidden(X4,k6_enumset1(X5,X5,X5,X5,X5,X3,X4,X3)) ),
    inference(superposition,[],[f60,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X1,X2,X0) ),
    inference(definition_unfolding,[],[f25,f42,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X4,X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X4,X2) != X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f24,f40])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK0,sK1))
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK0,sK1))
      | sK1 = X0
      | sK1 = X0
      | sK1 = X0 ) ),
    inference(superposition,[],[f63,f107])).

fof(f107,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK0,sK1) ),
    inference(superposition,[],[f106,f20])).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f106,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK0,sK1) ),
    inference(forward_demodulation,[],[f105,f48])).

fof(f105,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f46,f47])).

fof(f47,plain,(
    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f18,f45,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f41])).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f38,f23,f36,f43])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.53  % (4371)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.54  % (4378)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.54  % (4369)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.54  % (4370)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.54  % (4369)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f129,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(subsumption_resolution,[],[f127,f19])).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    sK0 != sK1),
% 0.23/0.54    inference(cnf_transformation,[],[f16])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.54    inference(ennf_transformation,[],[f15])).
% 0.23/0.54  fof(f15,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.23/0.54    inference(negated_conjecture,[],[f14])).
% 0.23/0.55  % (4386)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.55  % (4379)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.55  % (4386)Refutation not found, incomplete strategy% (4386)------------------------------
% 0.23/0.55  % (4386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (4378)Refutation not found, incomplete strategy% (4378)------------------------------
% 0.23/0.55  % (4378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (4378)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (4378)Memory used [KB]: 6140
% 0.23/0.55  % (4378)Time elapsed: 0.110 s
% 0.23/0.55  % (4378)------------------------------
% 0.23/0.55  % (4378)------------------------------
% 0.23/0.55  % (4386)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (4386)Memory used [KB]: 1663
% 0.23/0.55  % (4386)Time elapsed: 0.107 s
% 0.23/0.55  % (4386)------------------------------
% 0.23/0.55  % (4386)------------------------------
% 0.23/0.55  % (4377)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.56  % (4372)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.56  % (4387)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.56  % (4372)Refutation not found, incomplete strategy% (4372)------------------------------
% 0.23/0.56  % (4372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (4372)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (4372)Memory used [KB]: 10618
% 0.23/0.56  % (4372)Time elapsed: 0.094 s
% 0.23/0.56  % (4372)------------------------------
% 0.23/0.56  % (4372)------------------------------
% 0.23/0.56  % (4385)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.56  % (4365)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.56  fof(f14,conjecture,(
% 0.23/0.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.23/0.56  fof(f127,plain,(
% 0.23/0.56    sK0 = sK1),
% 0.23/0.56    inference(resolution,[],[f122,f68])).
% 0.23/0.56  fof(f68,plain,(
% 0.23/0.56    ( ! [X4,X5,X3] : (r2_hidden(X4,k6_enumset1(X5,X5,X5,X5,X5,X3,X4,X3))) )),
% 0.23/0.56    inference(superposition,[],[f60,f48])).
% 0.23/0.56  fof(f48,plain,(
% 0.23/0.56    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X1,X2,X0)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f25,f42,f42])).
% 0.23/0.56  fof(f42,plain,(
% 0.23/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f26,f40])).
% 0.23/0.56  fof(f40,plain,(
% 0.23/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f35,f36])).
% 0.23/0.56  fof(f36,plain,(
% 0.23/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f13])).
% 0.23/0.56  fof(f13,axiom,(
% 0.23/0.56    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).
% 0.23/0.56  fof(f35,plain,(
% 0.23/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f10])).
% 0.23/0.56  fof(f10,axiom,(
% 0.23/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.56  fof(f26,plain,(
% 0.23/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f9])).
% 0.23/0.56  fof(f9,axiom,(
% 0.23/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).
% 0.23/0.56  fof(f60,plain,(
% 0.23/0.56    ( ! [X4,X2,X0] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X4,X2))) )),
% 0.23/0.56    inference(equality_resolution,[],[f59])).
% 0.23/0.56  fof(f59,plain,(
% 0.23/0.56    ( ! [X4,X2,X0,X3] : (r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X4,X2) != X3) )),
% 0.23/0.56    inference(equality_resolution,[],[f50])).
% 0.23/0.56  fof(f50,plain,(
% 0.23/0.56    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.23/0.56    inference(definition_unfolding,[],[f33,f41])).
% 0.23/0.56  fof(f41,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f24,f40])).
% 0.23/0.56  fof(f24,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f12,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.23/0.56  fof(f33,plain,(
% 0.23/0.56    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.23/0.56    inference(cnf_transformation,[],[f17])).
% 0.23/0.56  fof(f17,plain,(
% 0.23/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.23/0.56    inference(ennf_transformation,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.23/0.56  fof(f122,plain,(
% 0.23/0.56    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK0,sK1)) | sK1 = X0) )),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f111])).
% 0.23/0.56  fof(f111,plain,(
% 0.23/0.56    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK0,sK1)) | sK1 = X0 | sK1 = X0 | sK1 = X0) )),
% 0.23/0.56    inference(superposition,[],[f63,f107])).
% 0.23/0.56  fof(f107,plain,(
% 0.23/0.56    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK0,sK1)),
% 0.23/0.56    inference(superposition,[],[f106,f20])).
% 0.23/0.56  fof(f20,plain,(
% 0.23/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.56    inference(cnf_transformation,[],[f1])).
% 0.23/0.56  fof(f1,axiom,(
% 0.23/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.23/0.56  fof(f106,plain,(
% 0.23/0.56    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK0,sK1)),
% 0.23/0.56    inference(forward_demodulation,[],[f105,f48])).
% 0.23/0.56  fof(f105,plain,(
% 0.23/0.56    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)),
% 0.23/0.56    inference(superposition,[],[f46,f47])).
% 0.23/0.56  fof(f47,plain,(
% 0.23/0.56    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.23/0.56    inference(definition_unfolding,[],[f18,f45,f45])).
% 0.23/0.56  fof(f45,plain,(
% 0.23/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f21,f43])).
% 0.23/0.56  fof(f43,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f22,f41])).
% 0.23/0.56  fof(f22,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f8])).
% 0.23/0.56  fof(f8,axiom,(
% 0.23/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.56  fof(f21,plain,(
% 0.23/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f7])).
% 0.23/0.56  fof(f7,axiom,(
% 0.23/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.56  fof(f18,plain,(
% 0.23/0.56    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.23/0.56    inference(cnf_transformation,[],[f16])).
% 0.23/0.56  fof(f46,plain,(
% 0.23/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) )),
% 0.23/0.56    inference(definition_unfolding,[],[f38,f23,f36,f43])).
% 0.23/0.56  fof(f23,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f2])).
% 0.23/0.56  fof(f2,axiom,(
% 0.23/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.23/0.56  fof(f38,plain,(
% 0.23/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.23/0.56  fof(f63,plain,(
% 0.23/0.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.23/0.56    inference(equality_resolution,[],[f52])).
% 0.23/0.56  fof(f52,plain,(
% 0.23/0.56    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.23/0.56    inference(definition_unfolding,[],[f31,f41])).
% 0.23/0.56  fof(f31,plain,(
% 0.23/0.56    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.23/0.56    inference(cnf_transformation,[],[f17])).
% 0.23/0.56  % SZS output end Proof for theBenchmark
% 0.23/0.56  % (4369)------------------------------
% 0.23/0.56  % (4369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (4369)Termination reason: Refutation
% 0.23/0.56  
% 0.23/0.56  % (4369)Memory used [KB]: 6268
% 0.23/0.56  % (4369)Time elapsed: 0.108 s
% 0.23/0.56  % (4369)------------------------------
% 0.23/0.56  % (4369)------------------------------
% 0.23/0.56  % (4388)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.56  % (4362)Success in time 0.189 s
%------------------------------------------------------------------------------
