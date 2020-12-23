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
% DateTime   : Thu Dec  3 12:41:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  59 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 (  97 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f180])).

fof(f180,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f22,f126])).

fof(f126,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f123,f83])).

fof(f83,plain,(
    ! [X2] : ~ r2_xboole_0(k3_tarski(k1_zfmisc_1(X2)),X2) ),
    inference(resolution,[],[f76,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,k3_tarski(k1_zfmisc_1(X1))) ),
    inference(resolution,[],[f74,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f74,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f23,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f25,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f123,plain,(
    ! [X0] :
      ( k3_tarski(k1_zfmisc_1(X0)) = X0
      | r2_xboole_0(k3_tarski(k1_zfmisc_1(X0)),X0) ) ),
    inference(resolution,[],[f122,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f122,plain,(
    ! [X0] : r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0)
      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) ) ),
    inference(resolution,[],[f52,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X3] :
      ( r1_tarski(sK1(k1_zfmisc_1(X2),X3),X2)
      | r1_tarski(k3_tarski(k1_zfmisc_1(X2)),X3) ) ),
    inference(resolution,[],[f27,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:15:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.50  % (27800)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.51  % (27806)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.51  % (27798)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.51  % (27814)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.52  % (27798)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % (27814)Refutation not found, incomplete strategy% (27814)------------------------------
% 0.23/0.52  % (27814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (27800)Refutation not found, incomplete strategy% (27800)------------------------------
% 0.23/0.52  % (27800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (27800)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (27800)Memory used [KB]: 10618
% 0.23/0.52  % (27800)Time elapsed: 0.093 s
% 0.23/0.52  % (27800)------------------------------
% 0.23/0.52  % (27800)------------------------------
% 0.23/0.52  % (27814)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (27814)Memory used [KB]: 10618
% 0.23/0.52  % (27814)Time elapsed: 0.095 s
% 0.23/0.52  % (27814)------------------------------
% 0.23/0.52  % (27814)------------------------------
% 0.23/0.52  % (27808)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.52  % (27816)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.53  % (27804)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (27811)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f186,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(trivial_inequality_removal,[],[f180])).
% 0.23/0.53  fof(f180,plain,(
% 0.23/0.53    sK0 != sK0),
% 0.23/0.53    inference(superposition,[],[f22,f126])).
% 0.23/0.53  fof(f126,plain,(
% 0.23/0.53    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f123,f83])).
% 0.23/0.53  fof(f83,plain,(
% 0.23/0.53    ( ! [X2] : (~r2_xboole_0(k3_tarski(k1_zfmisc_1(X2)),X2)) )),
% 0.23/0.53    inference(resolution,[],[f76,f34])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.23/0.53  fof(f76,plain,(
% 0.23/0.53    ( ! [X1] : (r1_tarski(X1,k3_tarski(k1_zfmisc_1(X1)))) )),
% 0.23/0.53    inference(resolution,[],[f74,f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,axiom,(
% 0.23/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.23/0.53  fof(f74,plain,(
% 0.23/0.53    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(resolution,[],[f47,f45])).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(definition_unfolding,[],[f23,f43])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f24,f42])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f35,f41])).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f39,f40])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,axiom,(
% 0.23/0.53    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,axiom,(
% 0.23/0.53    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f37,f44])).
% 0.23/0.53  fof(f44,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f25,f41])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f7])).
% 0.23/0.53  fof(f7,axiom,(
% 0.23/0.53    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.23/0.53  fof(f123,plain,(
% 0.23/0.53    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0 | r2_xboole_0(k3_tarski(k1_zfmisc_1(X0)),X0)) )),
% 0.23/0.53    inference(resolution,[],[f122,f29])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f20])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.53    inference(flattening,[],[f19])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.23/0.53    inference(ennf_transformation,[],[f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.23/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.23/0.53  fof(f122,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0)) )),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f118])).
% 0.23/0.53  fof(f118,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0)) )),
% 0.23/0.53    inference(resolution,[],[f52,f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(sK1(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,axiom,(
% 0.23/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    ( ! [X2,X3] : (r1_tarski(sK1(k1_zfmisc_1(X2),X3),X2) | r1_tarski(k3_tarski(k1_zfmisc_1(X2)),X3)) )),
% 0.23/0.53    inference(resolution,[],[f27,f49])).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.23/0.53    inference(equality_resolution,[],[f31])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,axiom,(
% 0.23/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f18])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    sK0 != k3_tarski(k1_zfmisc_1(sK0))),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0),
% 0.23/0.53    inference(ennf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,negated_conjecture,(
% 0.23/0.53    ~! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.23/0.53    inference(negated_conjecture,[],[f13])).
% 0.23/0.53  fof(f13,conjecture,(
% 0.23/0.53    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (27798)------------------------------
% 0.23/0.53  % (27798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (27798)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (27798)Memory used [KB]: 6268
% 0.23/0.53  % (27798)Time elapsed: 0.092 s
% 0.23/0.53  % (27798)------------------------------
% 0.23/0.53  % (27798)------------------------------
% 0.23/0.53  % (27791)Success in time 0.158 s
%------------------------------------------------------------------------------
