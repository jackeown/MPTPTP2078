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
% DateTime   : Thu Dec  3 12:38:35 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 225 expanded)
%              Number of leaves         :   16 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 270 expanded)
%              Number of equality atoms :   58 ( 217 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f709,plain,(
    $false ),
    inference(subsumption_resolution,[],[f708,f128])).

fof(f128,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f78,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f47,f75,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f78,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f43,f76,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f75])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f708,plain,(
    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f707,f153])).

fof(f153,plain,(
    ! [X1] : k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X1 ),
    inference(forward_demodulation,[],[f147,f79])).

fof(f79,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f45,f76])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f147,plain,(
    ! [X1] : k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f82,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f44,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f52,f76,f50,f76])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f707,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f700,f191])).

fof(f191,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f190,f94])).

fof(f190,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f187,f95])).

fof(f95,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f87,f56])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f187,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ),
    inference(superposition,[],[f81,f113])).

fof(f113,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f79,f80])).

fof(f81,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f51,f50,f50,f76])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f700,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f82,f163])).

fof(f163,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f108,f56])).

fof(f108,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f42,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f42,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (7978)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (7984)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (7991)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (8002)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (7981)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (7986)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (7982)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (7983)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (7979)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (7979)Refutation not found, incomplete strategy% (7979)------------------------------
% 0.22/0.53  % (7979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7979)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7979)Memory used [KB]: 1663
% 0.22/0.53  % (7979)Time elapsed: 0.115 s
% 0.22/0.53  % (7979)------------------------------
% 0.22/0.53  % (7979)------------------------------
% 0.22/0.53  % (8001)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (7993)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (7990)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (8006)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (7980)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (7994)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (7987)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (8004)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (7985)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (7995)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (8007)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (7998)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (8007)Refutation not found, incomplete strategy% (8007)------------------------------
% 0.22/0.54  % (8007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8007)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8007)Memory used [KB]: 1663
% 0.22/0.54  % (8007)Time elapsed: 0.141 s
% 0.22/0.54  % (8007)------------------------------
% 0.22/0.54  % (8007)------------------------------
% 0.22/0.55  % (8000)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (7995)Refutation not found, incomplete strategy% (7995)------------------------------
% 0.22/0.55  % (7995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7995)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7995)Memory used [KB]: 1663
% 0.22/0.55  % (7995)Time elapsed: 0.141 s
% 0.22/0.55  % (7995)------------------------------
% 0.22/0.55  % (7995)------------------------------
% 0.22/0.55  % (8003)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (7997)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.55  % (7990)Refutation not found, incomplete strategy% (7990)------------------------------
% 1.48/0.55  % (7990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (7990)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (7990)Memory used [KB]: 10618
% 1.48/0.55  % (7990)Time elapsed: 0.143 s
% 1.48/0.55  % (7990)------------------------------
% 1.48/0.55  % (7990)------------------------------
% 1.48/0.55  % (7999)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.48/0.55  % (7996)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.48/0.55  % (7988)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.48/0.55  % (8006)Refutation not found, incomplete strategy% (8006)------------------------------
% 1.48/0.55  % (8006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (8006)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (8006)Memory used [KB]: 10746
% 1.48/0.55  % (8006)Time elapsed: 0.152 s
% 1.48/0.55  % (8006)------------------------------
% 1.48/0.55  % (8006)------------------------------
% 1.48/0.56  % (8005)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.48/0.56  % (7988)Refutation not found, incomplete strategy% (7988)------------------------------
% 1.48/0.56  % (7988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (7988)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (7988)Memory used [KB]: 10746
% 1.48/0.56  % (7988)Time elapsed: 0.152 s
% 1.48/0.56  % (7988)------------------------------
% 1.48/0.56  % (7988)------------------------------
% 1.48/0.56  % (7989)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.56  % (7992)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.48/0.56  % (7994)Refutation not found, incomplete strategy% (7994)------------------------------
% 1.48/0.56  % (7994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (7994)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (7994)Memory used [KB]: 10618
% 1.48/0.56  % (7994)Time elapsed: 0.118 s
% 1.48/0.56  % (7994)------------------------------
% 1.48/0.56  % (7994)------------------------------
% 1.48/0.56  % (7982)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.57  % SZS output start Proof for theBenchmark
% 1.48/0.57  fof(f709,plain,(
% 1.48/0.57    $false),
% 1.48/0.57    inference(subsumption_resolution,[],[f708,f128])).
% 1.48/0.57  fof(f128,plain,(
% 1.48/0.57    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.48/0.57    inference(forward_demodulation,[],[f78,f80])).
% 1.48/0.57  fof(f80,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f47,f75,f75])).
% 1.48/0.57  fof(f75,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f48,f74])).
% 1.48/0.57  fof(f74,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f66,f73])).
% 1.48/0.57  fof(f73,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f18])).
% 1.48/0.57  fof(f18,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.48/0.57  fof(f66,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f17])).
% 1.48/0.57  fof(f17,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.57  fof(f48,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f16])).
% 1.48/0.57  fof(f16,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.57  fof(f47,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f14])).
% 1.48/0.57  fof(f14,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.48/0.57  fof(f78,plain,(
% 1.48/0.57    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.48/0.57    inference(definition_unfolding,[],[f43,f76,f77])).
% 1.48/0.57  fof(f77,plain,(
% 1.48/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f46,f75])).
% 1.48/0.57  fof(f46,plain,(
% 1.48/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f15])).
% 1.48/0.57  fof(f15,axiom,(
% 1.48/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.57  fof(f76,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f49,f75])).
% 1.48/0.57  fof(f49,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f20])).
% 1.48/0.57  fof(f20,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.48/0.57  fof(f43,plain,(
% 1.48/0.57    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.48/0.57    inference(cnf_transformation,[],[f30])).
% 1.48/0.57  fof(f30,plain,(
% 1.48/0.57    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f29])).
% 1.48/0.57  fof(f29,plain,(
% 1.48/0.57    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.48/0.57    introduced(choice_axiom,[])).
% 1.48/0.57  fof(f24,plain,(
% 1.48/0.57    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f22])).
% 1.48/0.57  fof(f22,negated_conjecture,(
% 1.48/0.57    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.48/0.57    inference(negated_conjecture,[],[f21])).
% 1.48/0.57  fof(f21,conjecture,(
% 1.48/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.48/0.57  fof(f708,plain,(
% 1.48/0.57    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.48/0.57    inference(forward_demodulation,[],[f707,f153])).
% 1.48/0.57  fof(f153,plain,(
% 1.48/0.57    ( ! [X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X1) )),
% 1.48/0.57    inference(forward_demodulation,[],[f147,f79])).
% 1.48/0.57  fof(f79,plain,(
% 1.48/0.57    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.48/0.57    inference(definition_unfolding,[],[f45,f76])).
% 1.48/0.57  fof(f45,plain,(
% 1.48/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f8])).
% 1.48/0.57  fof(f8,axiom,(
% 1.48/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.48/0.57  fof(f147,plain,(
% 1.48/0.57    ( ! [X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) )),
% 1.48/0.57    inference(superposition,[],[f82,f94])).
% 1.48/0.57  fof(f94,plain,(
% 1.48/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.48/0.57    inference(unit_resulting_resolution,[],[f44,f56])).
% 1.48/0.57  fof(f56,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f26])).
% 1.48/0.57  fof(f26,plain,(
% 1.48/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f9])).
% 1.48/0.57  fof(f9,axiom,(
% 1.48/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.48/0.57  fof(f44,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f10])).
% 1.48/0.57  fof(f10,axiom,(
% 1.48/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.48/0.57  fof(f82,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f52,f76,f50,f76])).
% 1.48/0.57  fof(f50,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f7])).
% 1.48/0.57  fof(f7,axiom,(
% 1.48/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.48/0.57  fof(f52,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f11])).
% 1.48/0.57  fof(f11,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.48/0.57  fof(f707,plain,(
% 1.48/0.57    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 1.48/0.57    inference(forward_demodulation,[],[f700,f191])).
% 1.48/0.57  fof(f191,plain,(
% 1.48/0.57    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X1,X1)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f190,f94])).
% 1.48/0.57  fof(f190,plain,(
% 1.48/0.57    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f187,f95])).
% 1.48/0.57  fof(f95,plain,(
% 1.48/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.48/0.57    inference(unit_resulting_resolution,[],[f87,f56])).
% 1.48/0.57  fof(f87,plain,(
% 1.48/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.57    inference(equality_resolution,[],[f60])).
% 1.48/0.57  fof(f60,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.48/0.57    inference(cnf_transformation,[],[f34])).
% 1.48/0.57  fof(f34,plain,(
% 1.48/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.57    inference(flattening,[],[f33])).
% 1.48/0.57  fof(f33,plain,(
% 1.48/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.57    inference(nnf_transformation,[],[f6])).
% 1.48/0.57  fof(f6,axiom,(
% 1.48/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.57  fof(f187,plain,(
% 1.48/0.57    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,k3_xboole_0(X1,X1))) )),
% 1.48/0.57    inference(superposition,[],[f81,f113])).
% 1.48/0.57  fof(f113,plain,(
% 1.48/0.57    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.48/0.57    inference(superposition,[],[f79,f80])).
% 1.48/0.57  fof(f81,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f51,f50,f50,f76])).
% 1.48/0.57  fof(f51,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f12])).
% 1.48/0.57  fof(f12,axiom,(
% 1.48/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.63/0.57  fof(f700,plain,(
% 1.63/0.57    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.63/0.57    inference(superposition,[],[f82,f163])).
% 1.63/0.57  fof(f163,plain,(
% 1.63/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.63/0.57    inference(unit_resulting_resolution,[],[f108,f56])).
% 1.63/0.57  fof(f108,plain,(
% 1.63/0.57    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.63/0.57    inference(unit_resulting_resolution,[],[f42,f85])).
% 1.63/0.57  fof(f85,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.63/0.57    inference(definition_unfolding,[],[f65,f77])).
% 1.63/0.57  fof(f65,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f36])).
% 1.63/0.57  fof(f36,plain,(
% 1.63/0.57    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.63/0.57    inference(nnf_transformation,[],[f19])).
% 1.63/0.57  fof(f19,axiom,(
% 1.63/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.63/0.57  fof(f42,plain,(
% 1.63/0.57    r2_hidden(sK0,sK1)),
% 1.63/0.57    inference(cnf_transformation,[],[f30])).
% 1.63/0.57  % SZS output end Proof for theBenchmark
% 1.63/0.57  % (7982)------------------------------
% 1.63/0.57  % (7982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (7982)Termination reason: Refutation
% 1.63/0.57  
% 1.63/0.57  % (7982)Memory used [KB]: 2046
% 1.63/0.57  % (7982)Time elapsed: 0.147 s
% 1.63/0.57  % (7982)------------------------------
% 1.63/0.57  % (7982)------------------------------
% 1.63/0.57  % (7977)Success in time 0.203 s
%------------------------------------------------------------------------------
