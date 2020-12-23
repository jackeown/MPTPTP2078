%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (1068 expanded)
%              Number of leaves         :   11 ( 353 expanded)
%              Depth                    :   15
%              Number of atoms          :  105 (1573 expanded)
%              Number of equality atoms :   78 (1475 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(subsumption_resolution,[],[f218,f168])).

fof(f168,plain,(
    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(global_subsumption,[],[f41,f148,f150,f152])).

fof(f152,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f40,f150])).

fof(f40,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f17,f37])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f150,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f39,f40,f148,f149])).

fof(f149,plain,
    ( sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f47,f77])).

fof(f77,plain,(
    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f73,f38])).

fof(f38,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f19,f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f35])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f19,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) ),
    inference(superposition,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f22,f36,f36])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f21,f36])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f37,f37])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f39,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f18,f37,f37])).

fof(f18,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f148,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f47,f54])).

fof(f54,plain,(
    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f42,f38])).

fof(f41,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f16,f37])).

fof(f16,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f218,plain,(
    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f208,f58])).

fof(f58,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f208,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f151,f192])).

fof(f192,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f148,f167])).

fof(f167,plain,(
    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f41,f150])).

fof(f151,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f38,f150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.34  % CPULimit   : 60
% 0.21/0.34  % WCLimit    : 600
% 0.21/0.34  % DateTime   : Tue Dec  1 16:28:40 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.51  % (2369)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (2360)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (2352)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (2346)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (2354)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (2369)Refutation not found, incomplete strategy% (2369)------------------------------
% 0.21/0.52  % (2369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2369)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2369)Memory used [KB]: 10746
% 0.21/0.52  % (2369)Time elapsed: 0.062 s
% 0.21/0.52  % (2369)------------------------------
% 0.21/0.52  % (2369)------------------------------
% 0.21/0.52  % (2359)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (2352)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f218,f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.53    inference(global_subsumption,[],[f41,f148,f150,f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.21/0.53    inference(backward_demodulation,[],[f40,f150])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.21/0.53    inference(definition_unfolding,[],[f17,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f20,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f24,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    k1_xboole_0 = sK2),
% 0.21/0.53    inference(global_subsumption,[],[f39,f40,f148,f149])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK2),
% 0.21/0.53    inference(resolution,[],[f47,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.53    inference(superposition,[],[f73,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f37,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f35])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) )),
% 0.21/0.53    inference(superposition,[],[f42,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f36,f36])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f36])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f29,f37,f37])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.53    inference(definition_unfolding,[],[f18,f37,f37])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f47,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.53    inference(superposition,[],[f42,f38])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 0.21/0.53    inference(definition_unfolding,[],[f16,f37])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f208,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 0.21/0.53    inference(resolution,[],[f44,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f28,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f36])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.53    inference(backward_demodulation,[],[f151,f192])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(global_subsumption,[],[f148,f167])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f41,f150])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))),
% 0.21/0.53    inference(backward_demodulation,[],[f38,f150])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2352)------------------------------
% 0.21/0.53  % (2352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2352)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2352)Memory used [KB]: 6396
% 0.21/0.53  % (2352)Time elapsed: 0.077 s
% 0.21/0.53  % (2352)------------------------------
% 0.21/0.53  % (2352)------------------------------
% 0.21/0.53  % (2342)Success in time 0.168 s
%------------------------------------------------------------------------------
