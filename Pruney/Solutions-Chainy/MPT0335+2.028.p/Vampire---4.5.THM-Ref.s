%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 130 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 248 expanded)
%              Number of equality atoms :   56 ( 167 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(global_subsumption,[],[f78,f278])).

fof(f278,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f259,f84])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f70,f75])).

fof(f75,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f34,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f53,f44,f44,f44,f44])).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f259,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[],[f95,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f44,f44])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f95,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)) ),
    inference(superposition,[],[f66,f92])).

fof(f92,plain,(
    sK0 = k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    inference(forward_demodulation,[],[f77,f63])).

fof(f63,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f35,f61,f44])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    sK0 = k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) ),
    inference(resolution,[],[f36,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f36,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f78,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f62,f63])).

fof(f62,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f37,f44,f61])).

fof(f37,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:09:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (1650)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  % (1650)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (1656)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (1658)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (1648)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (1669)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(global_subsumption,[],[f78,f278])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f259,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) )),
% 0.21/0.50    inference(superposition,[],[f70,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f34,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f48,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 0.21/0.50    inference(negated_conjecture,[],[f18])).
% 0.21/0.50  fof(f18,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f53,f44,f44,f44,f44])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.21/0.50    inference(superposition,[],[f95,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f41,f44,f44])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0))),
% 0.21/0.50    inference(superposition,[],[f66,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    sK0 = k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)),
% 0.21/0.50    inference(forward_demodulation,[],[f77,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(definition_unfolding,[],[f35,f61,f44])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f39,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f43,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f52,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    sK0 = k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0)),
% 0.21/0.50    inference(resolution,[],[f36,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1) )),
% 0.21/0.50    inference(definition_unfolding,[],[f46,f61])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    r2_hidden(sK3,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f42,f44])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(superposition,[],[f62,f63])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.21/0.50    inference(definition_unfolding,[],[f37,f44,f61])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1650)------------------------------
% 0.21/0.50  % (1650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1650)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1650)Memory used [KB]: 11001
% 0.21/0.50  % (1650)Time elapsed: 0.097 s
% 0.21/0.50  % (1650)------------------------------
% 0.21/0.50  % (1650)------------------------------
% 0.21/0.51  % (1647)Success in time 0.146 s
%------------------------------------------------------------------------------
