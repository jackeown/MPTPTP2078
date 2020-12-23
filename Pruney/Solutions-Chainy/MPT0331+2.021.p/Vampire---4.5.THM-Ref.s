%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:07 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 217 expanded)
%              Number of leaves         :   12 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  111 ( 374 expanded)
%              Number of equality atoms :   60 ( 226 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1330,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1329])).

fof(f1329,plain,(
    sK2 != sK2 ),
    inference(superposition,[],[f1257,f81])).

fof(f81,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f49,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f71,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f71,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f40,f49])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f25,f31,f31])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f38,f31])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1257,plain,(
    sK2 != k5_xboole_0(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f41,f1254])).

fof(f1254,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f1211,f81])).

fof(f1211,plain,(
    k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k1_xboole_0) ),
    inference(superposition,[],[f77,f659])).

fof(f659,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    inference(forward_demodulation,[],[f658,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f58,f76])).

fof(f76,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f72,f49])).

fof(f72,plain,(
    ! [X1] : k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,X1) ),
    inference(superposition,[],[f40,f58])).

fof(f658,plain,(
    ! [X0] : k3_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) = k5_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f649,f76])).

fof(f649,plain,(
    ! [X0] : k3_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) = k5_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    inference(superposition,[],[f95,f144])).

fof(f144,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(resolution,[],[f121,f21])).

fof(f21,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f121,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | k2_enumset1(X1,X1,X1,sK1) = k5_xboole_0(k2_enumset1(X1,X1,X1,sK1),k3_xboole_0(k2_enumset1(X1,X1,X1,sK1),sK2)) ) ),
    inference(resolution,[],[f44,f22])).

fof(f22,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k2_enumset1(X0,X0,X0,X1) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2))
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f29,f39,f31,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f95,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) ),
    inference(superposition,[],[f40,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f24,f31,f31])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0)) ),
    inference(resolution,[],[f74,f47])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f43,f40])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f41,plain,(
    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f23,f31,f39])).

fof(f23,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:01:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.20/0.52  % (958)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.20/0.53  % (964)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.20/0.54  % (932)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.20/0.54  % (934)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.20/0.54  % (942)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.54  % (971)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.20/0.54  % (965)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.54  % (939)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.39/0.55  % (933)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.55  % (968)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.55  % (940)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.39/0.55  % (945)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.55  % (966)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.39/0.55  % (962)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.55  % (962)Refutation not found, incomplete strategy% (962)------------------------------
% 1.39/0.55  % (962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (962)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (962)Memory used [KB]: 1663
% 1.39/0.55  % (962)Time elapsed: 0.137 s
% 1.39/0.55  % (962)------------------------------
% 1.39/0.55  % (962)------------------------------
% 1.39/0.55  % (932)Refutation not found, incomplete strategy% (932)------------------------------
% 1.39/0.55  % (932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (932)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (932)Memory used [KB]: 1663
% 1.39/0.55  % (931)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.55  % (932)Time elapsed: 0.134 s
% 1.39/0.55  % (932)------------------------------
% 1.39/0.55  % (932)------------------------------
% 1.39/0.55  % (960)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.55  % (948)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.39/0.55  % (946)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.55  % (960)Refutation not found, incomplete strategy% (960)------------------------------
% 1.39/0.55  % (960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (960)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (960)Memory used [KB]: 10618
% 1.39/0.55  % (960)Time elapsed: 0.136 s
% 1.39/0.55  % (960)------------------------------
% 1.39/0.55  % (960)------------------------------
% 1.39/0.56  % (961)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.56  % (946)Refutation not found, incomplete strategy% (946)------------------------------
% 1.39/0.56  % (946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (946)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (946)Memory used [KB]: 10746
% 1.39/0.56  % (946)Time elapsed: 0.136 s
% 1.39/0.56  % (946)------------------------------
% 1.39/0.56  % (946)------------------------------
% 1.39/0.56  % (948)Refutation not found, incomplete strategy% (948)------------------------------
% 1.39/0.56  % (948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (948)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (948)Memory used [KB]: 10618
% 1.39/0.56  % (948)Time elapsed: 0.140 s
% 1.39/0.56  % (948)------------------------------
% 1.39/0.56  % (948)------------------------------
% 1.39/0.56  % (947)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.56  % (969)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.56  % (963)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.56  % (969)Refutation not found, incomplete strategy% (969)------------------------------
% 1.39/0.56  % (969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (969)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (969)Memory used [KB]: 6140
% 1.39/0.56  % (969)Time elapsed: 0.139 s
% 1.39/0.56  % (969)------------------------------
% 1.39/0.56  % (969)------------------------------
% 1.39/0.56  % (944)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.56  % (972)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.56  % (967)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.56  % (972)Refutation not found, incomplete strategy% (972)------------------------------
% 1.39/0.56  % (972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (972)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (972)Memory used [KB]: 10746
% 1.39/0.56  % (972)Time elapsed: 0.140 s
% 1.39/0.56  % (972)------------------------------
% 1.39/0.56  % (972)------------------------------
% 1.39/0.56  % (971)Refutation not found, incomplete strategy% (971)------------------------------
% 1.39/0.56  % (971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (971)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (971)Memory used [KB]: 6140
% 1.39/0.56  % (971)Time elapsed: 0.145 s
% 1.39/0.56  % (971)------------------------------
% 1.39/0.56  % (971)------------------------------
% 1.39/0.56  % (949)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.57  % (970)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.57  % (970)Refutation not found, incomplete strategy% (970)------------------------------
% 1.39/0.57  % (970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (970)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (970)Memory used [KB]: 6268
% 1.39/0.57  % (970)Time elapsed: 0.150 s
% 1.39/0.57  % (970)------------------------------
% 1.39/0.57  % (970)------------------------------
% 1.39/0.57  % (943)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.58  % (959)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.58  % (973)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.58  % (973)Refutation not found, incomplete strategy% (973)------------------------------
% 1.39/0.58  % (973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (973)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  % (973)Memory used [KB]: 1663
% 1.39/0.58  % (973)Time elapsed: 0.001 s
% 1.39/0.58  % (973)------------------------------
% 1.39/0.58  % (973)------------------------------
% 1.39/0.60  % (940)Refutation found. Thanks to Tanya!
% 1.39/0.60  % SZS status Theorem for theBenchmark
% 1.39/0.60  % SZS output start Proof for theBenchmark
% 1.39/0.60  fof(f1330,plain,(
% 1.39/0.60    $false),
% 1.39/0.60    inference(trivial_inequality_removal,[],[f1329])).
% 1.39/0.60  fof(f1329,plain,(
% 1.39/0.60    sK2 != sK2),
% 1.39/0.60    inference(superposition,[],[f1257,f81])).
% 1.39/0.60  fof(f81,plain,(
% 1.39/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.39/0.60    inference(backward_demodulation,[],[f49,f75])).
% 1.39/0.60  fof(f75,plain,(
% 1.39/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.39/0.60    inference(forward_demodulation,[],[f71,f58])).
% 1.39/0.60  fof(f58,plain,(
% 1.39/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.39/0.60    inference(resolution,[],[f47,f50])).
% 1.39/0.60  fof(f50,plain,(
% 1.39/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.60    inference(equality_resolution,[],[f35])).
% 1.39/0.60  fof(f35,plain,(
% 1.39/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.60    inference(cnf_transformation,[],[f20])).
% 1.39/0.60  fof(f20,plain,(
% 1.39/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.60    inference(flattening,[],[f19])).
% 1.39/0.60  fof(f19,plain,(
% 1.39/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.60    inference(nnf_transformation,[],[f1])).
% 1.39/0.60  fof(f1,axiom,(
% 1.39/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.60  fof(f47,plain,(
% 1.39/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/0.60    inference(definition_unfolding,[],[f33,f31])).
% 1.39/0.60  fof(f31,plain,(
% 1.39/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/0.60    inference(cnf_transformation,[],[f3])).
% 1.39/0.60  fof(f3,axiom,(
% 1.39/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.39/0.60  fof(f33,plain,(
% 1.39/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f18])).
% 1.39/0.60  fof(f18,plain,(
% 1.39/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.39/0.60    inference(nnf_transformation,[],[f2])).
% 1.39/0.60  fof(f2,axiom,(
% 1.39/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.39/0.60  fof(f71,plain,(
% 1.39/0.60    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.39/0.60    inference(superposition,[],[f40,f49])).
% 1.39/0.60  fof(f40,plain,(
% 1.39/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.39/0.60    inference(definition_unfolding,[],[f25,f31,f31])).
% 1.39/0.60  fof(f25,plain,(
% 1.39/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.39/0.60    inference(cnf_transformation,[],[f6])).
% 1.39/0.60  fof(f6,axiom,(
% 1.39/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.39/0.60  fof(f49,plain,(
% 1.39/0.60    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.39/0.60    inference(definition_unfolding,[],[f38,f31])).
% 1.39/0.60  fof(f38,plain,(
% 1.39/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.39/0.60    inference(cnf_transformation,[],[f5])).
% 1.39/0.60  fof(f5,axiom,(
% 1.39/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.39/0.60  fof(f1257,plain,(
% 1.39/0.60    sK2 != k5_xboole_0(sK2,k1_xboole_0)),
% 1.39/0.60    inference(backward_demodulation,[],[f41,f1254])).
% 1.39/0.60  fof(f1254,plain,(
% 1.39/0.60    k1_xboole_0 = k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.39/0.60    inference(superposition,[],[f1211,f81])).
% 1.39/0.60  fof(f1211,plain,(
% 1.39/0.60    k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k1_xboole_0)),
% 1.39/0.60    inference(superposition,[],[f77,f659])).
% 1.39/0.60  fof(f659,plain,(
% 1.39/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)) )),
% 1.39/0.60    inference(forward_demodulation,[],[f658,f86])).
% 1.39/0.60  fof(f86,plain,(
% 1.39/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.39/0.60    inference(backward_demodulation,[],[f58,f76])).
% 1.39/0.60  fof(f76,plain,(
% 1.39/0.60    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.39/0.60    inference(forward_demodulation,[],[f72,f49])).
% 1.39/0.60  fof(f72,plain,(
% 1.39/0.60    ( ! [X1] : (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,X1)) )),
% 1.39/0.60    inference(superposition,[],[f40,f58])).
% 1.39/0.60  fof(f658,plain,(
% 1.39/0.60    ( ! [X0] : (k3_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) = k5_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)))) )),
% 1.39/0.60    inference(forward_demodulation,[],[f649,f76])).
% 1.39/0.60  fof(f649,plain,(
% 1.39/0.60    ( ! [X0] : (k3_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) = k5_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1)),k3_xboole_0(X0,k2_enumset1(sK0,sK0,sK0,sK1))))) )),
% 1.39/0.60    inference(superposition,[],[f95,f144])).
% 1.39/0.60  fof(f144,plain,(
% 1.39/0.60    k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 1.39/0.60    inference(resolution,[],[f121,f21])).
% 1.39/0.60  fof(f21,plain,(
% 1.39/0.60    ~r2_hidden(sK0,sK2)),
% 1.39/0.60    inference(cnf_transformation,[],[f15])).
% 1.39/0.60  fof(f15,plain,(
% 1.39/0.60    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 1.39/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 1.39/0.60  fof(f14,plain,(
% 1.39/0.60    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 1.39/0.60    introduced(choice_axiom,[])).
% 1.39/0.60  fof(f13,plain,(
% 1.39/0.60    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.39/0.60    inference(ennf_transformation,[],[f12])).
% 1.39/0.60  fof(f12,negated_conjecture,(
% 1.39/0.60    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.39/0.60    inference(negated_conjecture,[],[f11])).
% 1.39/0.60  fof(f11,conjecture,(
% 1.39/0.60    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.39/0.60  fof(f121,plain,(
% 1.39/0.60    ( ! [X1] : (r2_hidden(X1,sK2) | k2_enumset1(X1,X1,X1,sK1) = k5_xboole_0(k2_enumset1(X1,X1,X1,sK1),k3_xboole_0(k2_enumset1(X1,X1,X1,sK1),sK2))) )),
% 1.39/0.60    inference(resolution,[],[f44,f22])).
% 1.39/0.60  fof(f22,plain,(
% 1.39/0.60    ~r2_hidden(sK1,sK2)),
% 1.39/0.60    inference(cnf_transformation,[],[f15])).
% 1.39/0.60  fof(f44,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k2_enumset1(X0,X0,X0,X1) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) | r2_hidden(X0,X2)) )),
% 1.39/0.60    inference(definition_unfolding,[],[f29,f39,f31,f39])).
% 1.39/0.60  fof(f39,plain,(
% 1.39/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.39/0.60    inference(definition_unfolding,[],[f30,f37])).
% 1.39/0.60  fof(f37,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f9])).
% 1.39/0.60  fof(f9,axiom,(
% 1.39/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.60  fof(f30,plain,(
% 1.39/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f8])).
% 1.39/0.60  fof(f8,axiom,(
% 1.39/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.60  fof(f29,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f17])).
% 1.39/0.60  fof(f17,plain,(
% 1.39/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.39/0.60    inference(flattening,[],[f16])).
% 1.39/0.60  fof(f16,plain,(
% 1.39/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.39/0.60    inference(nnf_transformation,[],[f10])).
% 1.39/0.60  fof(f10,axiom,(
% 1.39/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.39/0.60  fof(f95,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))))) )),
% 1.39/0.60    inference(superposition,[],[f40,f42])).
% 1.39/0.60  fof(f42,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.39/0.60    inference(definition_unfolding,[],[f24,f31,f31])).
% 1.39/0.60  fof(f24,plain,(
% 1.39/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f7])).
% 1.39/0.60  fof(f7,axiom,(
% 1.39/0.60    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.39/0.60  fof(f77,plain,(
% 1.39/0.60    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) )),
% 1.39/0.60    inference(resolution,[],[f74,f47])).
% 1.39/0.60  fof(f74,plain,(
% 1.39/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.39/0.60    inference(superposition,[],[f43,f40])).
% 1.39/0.60  fof(f43,plain,(
% 1.39/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.39/0.60    inference(definition_unfolding,[],[f26,f31])).
% 1.39/0.60  fof(f26,plain,(
% 1.39/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.39/0.60    inference(cnf_transformation,[],[f4])).
% 1.39/0.60  fof(f4,axiom,(
% 1.39/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.39/0.60  fof(f41,plain,(
% 1.39/0.60    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.39/0.60    inference(definition_unfolding,[],[f23,f31,f39])).
% 1.39/0.60  fof(f23,plain,(
% 1.39/0.60    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 1.39/0.60    inference(cnf_transformation,[],[f15])).
% 1.39/0.60  % SZS output end Proof for theBenchmark
% 1.39/0.60  % (940)------------------------------
% 1.39/0.60  % (940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.60  % (940)Termination reason: Refutation
% 1.39/0.60  
% 1.39/0.60  % (940)Memory used [KB]: 2302
% 1.39/0.60  % (940)Time elapsed: 0.168 s
% 1.39/0.60  % (940)------------------------------
% 1.39/0.60  % (940)------------------------------
% 1.39/0.60  % (930)Success in time 0.231 s
%------------------------------------------------------------------------------
