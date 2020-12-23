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
% DateTime   : Thu Dec  3 12:39:40 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 720 expanded)
%              Number of leaves         :   14 ( 225 expanded)
%              Depth                    :   18
%              Number of atoms          :  122 ( 959 expanded)
%              Number of equality atoms :   67 ( 701 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f291,f119])).

fof(f119,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f116,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f39,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f116,plain,(
    ! [X0] : ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f114,f24])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_enumset1(X0,X0,X0)) ) ),
    inference(extensionality_resolution,[],[f34,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f43,f60])).

fof(f60,plain,(
    ! [X1] : k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f26,f40,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f291,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f57,f270])).

fof(f270,plain,(
    k1_xboole_0 = k1_enumset1(sK0,sK0,sK1) ),
    inference(superposition,[],[f261,f65])).

fof(f65,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f44,f59])).

fof(f59,plain,(
    ! [X0] : k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(resolution,[],[f46,f24])).

fof(f44,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f27,f40,f40])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f261,plain,(
    k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f42,f257])).

fof(f257,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f209,f251])).

fof(f251,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f212,f204])).

fof(f204,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) ),
    inference(backward_demodulation,[],[f121,f172])).

fof(f172,plain,(
    ! [X0] : k4_xboole_0(X0,sK2) = X0 ),
    inference(superposition,[],[f126,f170])).

fof(f170,plain,(
    ! [X0] : k4_xboole_0(k4_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)),sK2) = X0 ),
    inference(forward_demodulation,[],[f132,f144])).

fof(f144,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f140,f78])).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f45,f59])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f140,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f78,f126])).

fof(f132,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)),sK2) ),
    inference(superposition,[],[f120,f77])).

fof(f77,plain,(
    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1))) ),
    inference(superposition,[],[f45,f42])).

fof(f120,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f47,f45])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f126,plain,(
    ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6) ),
    inference(superposition,[],[f120,f91])).

fof(f91,plain,(
    ! [X1] : k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(resolution,[],[f76,f51])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(backward_demodulation,[],[f46,f45])).

fof(f121,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(superposition,[],[f64,f45])).

fof(f64,plain,(
    k1_xboole_0 = k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))) ),
    inference(superposition,[],[f44,f42])).

fof(f212,plain,(
    ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f36,f206])).

fof(f206,plain,(
    sK2 = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f91,f172])).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f209,plain,(
    sK2 = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f82,f172])).

fof(f82,plain,(
    ! [X8] : k5_xboole_0(X8,k4_xboole_0(k1_xboole_0,X8)) = X8 ),
    inference(superposition,[],[f45,f65])).

fof(f42,plain,(
    k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f23,f40,f29])).

fof(f23,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(resolution,[],[f49,f51])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f38,f29])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:09:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (12154)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (12148)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (12148)Refutation not found, incomplete strategy% (12148)------------------------------
% 0.21/0.53  % (12148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12148)Memory used [KB]: 1663
% 0.21/0.53  % (12148)Time elapsed: 0.109 s
% 0.21/0.53  % (12148)------------------------------
% 0.21/0.53  % (12148)------------------------------
% 0.21/0.53  % (12155)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (12149)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (12147)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (12172)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (12163)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (12163)Refutation not found, incomplete strategy% (12163)------------------------------
% 0.21/0.54  % (12163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12163)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12163)Memory used [KB]: 10618
% 0.21/0.54  % (12163)Time elapsed: 0.129 s
% 0.21/0.54  % (12163)------------------------------
% 0.21/0.54  % (12163)------------------------------
% 0.21/0.54  % (12164)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (12159)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (12150)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (12156)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.54  % (12165)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.40/0.54  % (12158)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.40/0.54  % (12165)Refutation not found, incomplete strategy% (12165)------------------------------
% 1.40/0.54  % (12165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (12165)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (12165)Memory used [KB]: 1663
% 1.40/0.54  % (12165)Time elapsed: 0.139 s
% 1.40/0.54  % (12165)------------------------------
% 1.40/0.54  % (12165)------------------------------
% 1.40/0.54  % (12162)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.40/0.54  % (12172)Refutation not found, incomplete strategy% (12172)------------------------------
% 1.40/0.54  % (12172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (12172)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (12172)Memory used [KB]: 6140
% 1.40/0.54  % (12172)Time elapsed: 0.126 s
% 1.40/0.54  % (12172)------------------------------
% 1.40/0.54  % (12172)------------------------------
% 1.40/0.55  % (12173)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.55  % (12176)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.55  % (12176)Refutation not found, incomplete strategy% (12176)------------------------------
% 1.40/0.55  % (12176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (12176)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (12176)Memory used [KB]: 1663
% 1.40/0.55  % (12176)Time elapsed: 0.001 s
% 1.40/0.55  % (12176)------------------------------
% 1.40/0.55  % (12176)------------------------------
% 1.40/0.55  % (12173)Refutation not found, incomplete strategy% (12173)------------------------------
% 1.40/0.55  % (12173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (12173)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (12173)Memory used [KB]: 6140
% 1.40/0.55  % (12173)Time elapsed: 0.148 s
% 1.40/0.55  % (12173)------------------------------
% 1.40/0.55  % (12173)------------------------------
% 1.40/0.55  % (12164)Refutation not found, incomplete strategy% (12164)------------------------------
% 1.40/0.55  % (12164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (12164)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (12164)Memory used [KB]: 1663
% 1.40/0.55  % (12164)Time elapsed: 0.127 s
% 1.40/0.55  % (12164)------------------------------
% 1.40/0.55  % (12164)------------------------------
% 1.40/0.55  % (12160)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.55  % (12157)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.40/0.55  % (12151)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.40/0.55  % (12168)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.40/0.55  % (12157)Refutation not found, incomplete strategy% (12157)------------------------------
% 1.40/0.55  % (12157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (12157)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (12157)Memory used [KB]: 10746
% 1.40/0.55  % (12157)Time elapsed: 0.153 s
% 1.40/0.55  % (12157)------------------------------
% 1.40/0.55  % (12157)------------------------------
% 1.40/0.55  % (12170)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.40/0.55  % (12174)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.40/0.55  % (12174)Refutation not found, incomplete strategy% (12174)------------------------------
% 1.40/0.55  % (12174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (12174)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (12174)Memory used [KB]: 6140
% 1.40/0.55  % (12174)Time elapsed: 0.147 s
% 1.40/0.55  % (12174)------------------------------
% 1.40/0.55  % (12174)------------------------------
% 1.40/0.55  % (12153)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.56  % (12166)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.56  % (12166)Refutation not found, incomplete strategy% (12166)------------------------------
% 1.40/0.56  % (12166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (12166)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (12166)Memory used [KB]: 1663
% 1.40/0.56  % (12166)Time elapsed: 0.160 s
% 1.40/0.56  % (12166)------------------------------
% 1.40/0.56  % (12166)------------------------------
% 1.40/0.56  % (12152)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.40/0.56  % (12152)Refutation not found, incomplete strategy% (12152)------------------------------
% 1.40/0.56  % (12152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (12159)Refutation not found, incomplete strategy% (12159)------------------------------
% 1.40/0.57  % (12159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (12159)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (12159)Memory used [KB]: 10618
% 1.40/0.57  % (12159)Time elapsed: 0.136 s
% 1.40/0.57  % (12159)------------------------------
% 1.40/0.57  % (12159)------------------------------
% 1.40/0.57  % (12152)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (12152)Memory used [KB]: 1663
% 1.40/0.57  % (12152)Time elapsed: 0.130 s
% 1.40/0.57  % (12152)------------------------------
% 1.40/0.57  % (12152)------------------------------
% 1.64/0.57  % (12169)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.64/0.57  % (12161)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.64/0.57  % (12161)Refutation not found, incomplete strategy% (12161)------------------------------
% 1.64/0.57  % (12161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (12170)Refutation not found, incomplete strategy% (12170)------------------------------
% 1.64/0.57  % (12170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (12170)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (12170)Memory used [KB]: 10746
% 1.64/0.57  % (12170)Time elapsed: 0.142 s
% 1.64/0.57  % (12170)------------------------------
% 1.64/0.57  % (12170)------------------------------
% 1.64/0.57  % (12175)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.64/0.58  % (12153)Refutation found. Thanks to Tanya!
% 1.64/0.58  % SZS status Theorem for theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f296,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(subsumption_resolution,[],[f291,f119])).
% 1.64/0.58  fof(f119,plain,(
% 1.64/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.64/0.58    inference(duplicate_literal_removal,[],[f118])).
% 1.64/0.58  fof(f118,plain,(
% 1.64/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.64/0.58    inference(resolution,[],[f116,f48])).
% 1.64/0.58  fof(f48,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f39,f29])).
% 1.64/0.58  fof(f29,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f9])).
% 1.64/0.58  fof(f9,axiom,(
% 1.64/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.58  fof(f39,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f22])).
% 1.64/0.58  fof(f22,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.64/0.58    inference(flattening,[],[f21])).
% 1.64/0.58  fof(f21,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.64/0.58    inference(nnf_transformation,[],[f11])).
% 1.64/0.58  fof(f11,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.64/0.58  fof(f116,plain,(
% 1.64/0.58    ( ! [X0] : (~r1_tarski(k1_enumset1(X0,X0,X0),k1_xboole_0)) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f114,f24])).
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f4])).
% 1.64/0.58  fof(f4,axiom,(
% 1.64/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.64/0.58  fof(f114,plain,(
% 1.64/0.58    ( ! [X0] : (~r1_tarski(k1_enumset1(X0,X0,X0),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_enumset1(X0,X0,X0))) )),
% 1.64/0.58    inference(extensionality_resolution,[],[f34,f105])).
% 1.64/0.58  fof(f105,plain,(
% 1.64/0.58    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 1.64/0.58    inference(superposition,[],[f43,f60])).
% 1.64/0.58  fof(f60,plain,(
% 1.64/0.58    ( ! [X1] : (k3_tarski(k1_enumset1(X1,X1,X1)) = X1) )),
% 1.64/0.58    inference(resolution,[],[f46,f51])).
% 1.64/0.58  fof(f51,plain,(
% 1.64/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.64/0.58    inference(equality_resolution,[],[f33])).
% 1.64/0.58  fof(f33,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.64/0.58    inference(cnf_transformation,[],[f20])).
% 1.64/0.58  fof(f20,plain,(
% 1.64/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.58    inference(flattening,[],[f19])).
% 1.64/0.58  fof(f19,plain,(
% 1.64/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.58    inference(nnf_transformation,[],[f2])).
% 1.64/0.58  fof(f2,axiom,(
% 1.64/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.64/0.58  fof(f46,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1) )),
% 1.64/0.58    inference(definition_unfolding,[],[f31,f40])).
% 1.64/0.58  fof(f40,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f28,f29])).
% 1.64/0.58  fof(f28,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f10])).
% 1.64/0.58  fof(f10,axiom,(
% 1.64/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.64/0.58  fof(f31,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f16])).
% 1.64/0.58  fof(f16,plain,(
% 1.64/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f3])).
% 1.64/0.58  fof(f3,axiom,(
% 1.64/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.64/0.58  fof(f43,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f26,f40,f41])).
% 1.64/0.58  fof(f41,plain,(
% 1.64/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f25,f29])).
% 1.64/0.58  fof(f25,plain,(
% 1.64/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.64/0.58  fof(f26,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f12])).
% 1.64/0.58  fof(f12,axiom,(
% 1.64/0.58    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.64/0.58  fof(f34,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f20])).
% 1.64/0.58  fof(f291,plain,(
% 1.64/0.58    r2_hidden(sK1,k1_xboole_0)),
% 1.64/0.58    inference(superposition,[],[f57,f270])).
% 1.64/0.58  fof(f270,plain,(
% 1.64/0.58    k1_xboole_0 = k1_enumset1(sK0,sK0,sK1)),
% 1.64/0.58    inference(superposition,[],[f261,f65])).
% 1.64/0.58  fof(f65,plain,(
% 1.64/0.58    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 1.64/0.58    inference(superposition,[],[f44,f59])).
% 1.64/0.58  fof(f59,plain,(
% 1.64/0.58    ( ! [X0] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.64/0.58    inference(resolution,[],[f46,f24])).
% 1.64/0.58  fof(f44,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f27,f40,f40])).
% 1.64/0.58  fof(f27,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.64/0.58  fof(f261,plain,(
% 1.64/0.58    k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),k1_xboole_0))),
% 1.64/0.58    inference(backward_demodulation,[],[f42,f257])).
% 1.64/0.58  fof(f257,plain,(
% 1.64/0.58    k1_xboole_0 = sK2),
% 1.64/0.58    inference(backward_demodulation,[],[f209,f251])).
% 1.64/0.58  fof(f251,plain,(
% 1.64/0.58    k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0)),
% 1.64/0.58    inference(superposition,[],[f212,f204])).
% 1.64/0.58  fof(f204,plain,(
% 1.64/0.58    k1_xboole_0 = k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1))),
% 1.64/0.58    inference(backward_demodulation,[],[f121,f172])).
% 1.64/0.58  fof(f172,plain,(
% 1.64/0.58    ( ! [X0] : (k4_xboole_0(X0,sK2) = X0) )),
% 1.64/0.58    inference(superposition,[],[f126,f170])).
% 1.64/0.58  fof(f170,plain,(
% 1.64/0.58    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)),sK2) = X0) )),
% 1.64/0.58    inference(forward_demodulation,[],[f132,f144])).
% 1.64/0.58  fof(f144,plain,(
% 1.64/0.58    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 1.64/0.58    inference(forward_demodulation,[],[f140,f78])).
% 1.64/0.58  fof(f78,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.64/0.58    inference(superposition,[],[f45,f59])).
% 1.64/0.58  fof(f45,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f30,f40])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f7])).
% 1.64/0.58  fof(f7,axiom,(
% 1.64/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.64/0.58  fof(f140,plain,(
% 1.64/0.58    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X3,k1_xboole_0))) )),
% 1.64/0.58    inference(superposition,[],[f78,f126])).
% 1.64/0.58  fof(f132,plain,(
% 1.64/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)),sK2)) )),
% 1.64/0.58    inference(superposition,[],[f120,f77])).
% 1.64/0.58  fof(f77,plain,(
% 1.64/0.58    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)))),
% 1.64/0.58    inference(superposition,[],[f45,f42])).
% 1.64/0.58  fof(f120,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 1.64/0.58    inference(forward_demodulation,[],[f47,f45])).
% 1.64/0.58  fof(f47,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f35,f40])).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f5])).
% 1.64/0.58  fof(f5,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.64/0.58  fof(f126,plain,(
% 1.64/0.58    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6)) )),
% 1.64/0.58    inference(superposition,[],[f120,f91])).
% 1.64/0.58  fof(f91,plain,(
% 1.64/0.58    ( ! [X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 1.64/0.58    inference(resolution,[],[f76,f51])).
% 1.64/0.58  fof(f76,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 1.64/0.58    inference(backward_demodulation,[],[f46,f45])).
% 1.64/0.58  fof(f121,plain,(
% 1.64/0.58    k1_xboole_0 = k5_xboole_0(sK2,k4_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.64/0.58    inference(superposition,[],[f64,f45])).
% 1.64/0.58  fof(f64,plain,(
% 1.64/0.58    k1_xboole_0 = k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1)))),
% 1.64/0.58    inference(superposition,[],[f44,f42])).
% 1.64/0.58  fof(f212,plain,(
% 1.64/0.58    ( ! [X0] : (k5_xboole_0(sK2,X0) = k5_xboole_0(sK2,k5_xboole_0(sK2,X0))) )),
% 1.64/0.58    inference(superposition,[],[f36,f206])).
% 1.64/0.58  fof(f206,plain,(
% 1.64/0.58    sK2 = k5_xboole_0(sK2,sK2)),
% 1.64/0.58    inference(superposition,[],[f91,f172])).
% 1.64/0.58  fof(f36,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f6])).
% 1.64/0.58  fof(f6,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.64/0.58  fof(f209,plain,(
% 1.64/0.58    sK2 = k5_xboole_0(sK2,k1_xboole_0)),
% 1.64/0.58    inference(superposition,[],[f82,f172])).
% 1.64/0.58  fof(f82,plain,(
% 1.64/0.58    ( ! [X8] : (k5_xboole_0(X8,k4_xboole_0(k1_xboole_0,X8)) = X8) )),
% 1.64/0.58    inference(superposition,[],[f45,f65])).
% 1.64/0.58  fof(f42,plain,(
% 1.64/0.58    k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.64/0.58    inference(definition_unfolding,[],[f23,f40,f29])).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.64/0.58    inference(cnf_transformation,[],[f18])).
% 1.64/0.58  fof(f18,plain,(
% 1.64/0.58    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 1.64/0.58  fof(f17,plain,(
% 1.64/0.58    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f15,plain,(
% 1.64/0.58    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.64/0.58    inference(ennf_transformation,[],[f14])).
% 1.64/0.58  fof(f14,negated_conjecture,(
% 1.64/0.58    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.64/0.58    inference(negated_conjecture,[],[f13])).
% 1.64/0.58  fof(f13,conjecture,(
% 1.64/0.58    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.64/0.58  fof(f57,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 1.64/0.58    inference(resolution,[],[f49,f51])).
% 1.64/0.58  fof(f49,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.64/0.58    inference(definition_unfolding,[],[f38,f29])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f22])).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (12153)------------------------------
% 1.64/0.58  % (12153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (12153)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (12153)Memory used [KB]: 10874
% 1.64/0.58  % (12153)Time elapsed: 0.173 s
% 1.64/0.58  % (12153)------------------------------
% 1.64/0.58  % (12153)------------------------------
% 1.64/0.58  % (12161)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (12161)Memory used [KB]: 1663
% 1.64/0.58  % (12161)Time elapsed: 0.167 s
% 1.64/0.58  % (12161)------------------------------
% 1.64/0.58  % (12161)------------------------------
% 1.64/0.58  % (12167)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.64/0.58  % (12175)Refutation not found, incomplete strategy% (12175)------------------------------
% 1.64/0.58  % (12175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (12175)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (12175)Memory used [KB]: 10746
% 1.64/0.58  % (12175)Time elapsed: 0.182 s
% 1.64/0.58  % (12175)------------------------------
% 1.64/0.58  % (12175)------------------------------
% 1.64/0.59  % (12146)Success in time 0.225 s
%------------------------------------------------------------------------------
