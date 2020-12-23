%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:40 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 339 expanded)
%              Number of leaves         :   18 ( 114 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 389 expanded)
%              Number of equality atoms :   66 ( 330 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f600,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f39,f459,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f72])).

% (5018)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (5024)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (5026)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (5039)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (5016)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f459,plain,(
    ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f458])).

fof(f458,plain,
    ( sK2 != sK2
    | ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(superposition,[],[f150,f437])).

fof(f437,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f429,f74])).

fof(f74,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f41,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f429,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f129,f393])).

fof(f393,plain,(
    ! [X15] : k1_xboole_0 = k5_xboole_0(X15,X15) ),
    inference(forward_demodulation,[],[f392,f207])).

fof(f207,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f202,f127])).

fof(f127,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f116,f74])).

fof(f116,plain,(
    ! [X6,X5] : r1_tarski(X5,k3_tarski(k3_enumset1(X6,X6,X6,X6,X5))) ),
    inference(superposition,[],[f75,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f44,f70,f70])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f202,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f133,f117])).

fof(f117,plain,(
    ! [X9] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X9)) = X9 ),
    inference(superposition,[],[f74,f76])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X0,X0))) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f80,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f51,f71,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f392,plain,(
    ! [X15] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X15,X15) ),
    inference(forward_demodulation,[],[f391,f153])).

fof(f153,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f117,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f391,plain,(
    ! [X15] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X15)) = k5_xboole_0(X15,X15) ),
    inference(subsumption_resolution,[],[f381,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f381,plain,(
    ! [X15] :
      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X15)) = k5_xboole_0(X15,X15)
      | ~ r1_tarski(X15,X15) ) ),
    inference(superposition,[],[f141,f117])).

fof(f141,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1) ) ),
    inference(superposition,[],[f78,f52])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f49,f48,f48,f71])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f129,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f79,f52])).

fof(f79,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f50,f71,f48,f71])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f150,plain,(
    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f73,f76])).

fof(f73,plain,(
    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f40,f71,f72])).

fof(f40,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f39,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:44:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (5014)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (5022)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (5017)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (5030)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (5025)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (5013)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (5036)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (5037)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (5033)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (5033)Refutation not found, incomplete strategy% (5033)------------------------------
% 0.21/0.52  % (5033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5033)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5033)Memory used [KB]: 10746
% 0.21/0.52  % (5033)Time elapsed: 0.126 s
% 0.21/0.52  % (5033)------------------------------
% 0.21/0.52  % (5033)------------------------------
% 0.21/0.52  % (5020)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (5023)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (5012)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (5015)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (5040)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (5031)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (5028)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (5027)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (5035)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (5029)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (5019)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (5038)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (5021)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (5021)Refutation not found, incomplete strategy% (5021)------------------------------
% 0.21/0.56  % (5021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5021)Memory used [KB]: 10618
% 0.21/0.56  % (5021)Time elapsed: 0.150 s
% 0.21/0.56  % (5021)------------------------------
% 0.21/0.56  % (5021)------------------------------
% 0.21/0.56  % (5011)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (5034)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.55/0.57  % (5032)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.55/0.57  % (5040)Refutation found. Thanks to Tanya!
% 1.55/0.57  % SZS status Theorem for theBenchmark
% 1.55/0.57  % SZS output start Proof for theBenchmark
% 1.55/0.57  fof(f600,plain,(
% 1.55/0.57    $false),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f39,f459,f81])).
% 1.55/0.57  fof(f81,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f60,f72])).
% 1.55/0.57  % (5018)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.55/0.57  % (5024)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.55/0.59  % (5026)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.55/0.59  % (5039)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.76/0.59  % (5016)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.76/0.59  fof(f72,plain,(
% 1.76/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.76/0.59    inference(definition_unfolding,[],[f42,f70])).
% 1.76/0.59  fof(f70,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.76/0.59    inference(definition_unfolding,[],[f46,f69])).
% 1.76/0.59  fof(f69,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.76/0.59    inference(definition_unfolding,[],[f61,f68])).
% 1.76/0.59  fof(f68,plain,(
% 1.76/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f16])).
% 1.76/0.59  fof(f16,axiom,(
% 1.76/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.76/0.59  fof(f61,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f15])).
% 1.76/0.59  fof(f15,axiom,(
% 1.76/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.76/0.59  fof(f46,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f14])).
% 1.76/0.59  fof(f14,axiom,(
% 1.76/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.76/0.59  fof(f42,plain,(
% 1.76/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f13])).
% 1.76/0.59  fof(f13,axiom,(
% 1.76/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.76/0.59  fof(f60,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f35])).
% 1.76/0.59  fof(f35,plain,(
% 1.76/0.59    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.76/0.59    inference(nnf_transformation,[],[f17])).
% 1.76/0.59  fof(f17,axiom,(
% 1.76/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.76/0.59  fof(f459,plain,(
% 1.76/0.59    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.76/0.59    inference(trivial_inequality_removal,[],[f458])).
% 1.76/0.59  fof(f458,plain,(
% 1.76/0.59    sK2 != sK2 | ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.76/0.59    inference(superposition,[],[f150,f437])).
% 1.76/0.59  fof(f437,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.76/0.59    inference(forward_demodulation,[],[f429,f74])).
% 1.76/0.59  fof(f74,plain,(
% 1.76/0.59    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.76/0.59    inference(definition_unfolding,[],[f41,f71])).
% 1.76/0.59  fof(f71,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.76/0.59    inference(definition_unfolding,[],[f47,f70])).
% 1.76/0.59  fof(f47,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.76/0.59    inference(cnf_transformation,[],[f18])).
% 1.76/0.59  fof(f18,axiom,(
% 1.76/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.76/0.59  fof(f41,plain,(
% 1.76/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.76/0.59    inference(cnf_transformation,[],[f5])).
% 1.76/0.59  fof(f5,axiom,(
% 1.76/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.76/0.59  fof(f429,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) | ~r1_tarski(X0,X1)) )),
% 1.76/0.59    inference(backward_demodulation,[],[f129,f393])).
% 1.76/0.59  fof(f393,plain,(
% 1.76/0.59    ( ! [X15] : (k1_xboole_0 = k5_xboole_0(X15,X15)) )),
% 1.76/0.59    inference(forward_demodulation,[],[f392,f207])).
% 1.76/0.59  fof(f207,plain,(
% 1.76/0.59    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.76/0.59    inference(subsumption_resolution,[],[f202,f127])).
% 1.76/0.59  fof(f127,plain,(
% 1.76/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.76/0.59    inference(superposition,[],[f116,f74])).
% 1.76/0.59  fof(f116,plain,(
% 1.76/0.59    ( ! [X6,X5] : (r1_tarski(X5,k3_tarski(k3_enumset1(X6,X6,X6,X6,X5)))) )),
% 1.76/0.59    inference(superposition,[],[f75,f76])).
% 1.76/0.59  fof(f76,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.76/0.59    inference(definition_unfolding,[],[f44,f70,f70])).
% 1.76/0.59  fof(f44,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f12])).
% 1.76/0.59  fof(f12,axiom,(
% 1.76/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.76/0.59  fof(f75,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.76/0.59    inference(definition_unfolding,[],[f43,f71])).
% 1.76/0.59  fof(f43,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.76/0.59    inference(cnf_transformation,[],[f11])).
% 1.76/0.59  fof(f11,axiom,(
% 1.76/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.76/0.59  fof(f202,plain,(
% 1.76/0.59    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X1)) )),
% 1.76/0.59    inference(superposition,[],[f133,f117])).
% 1.76/0.59  fof(f117,plain,(
% 1.76/0.59    ( ! [X9] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X9)) = X9) )),
% 1.76/0.59    inference(superposition,[],[f74,f76])).
% 1.76/0.59  fof(f133,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X0,X0))) = X0 | ~r1_tarski(X0,X1)) )),
% 1.76/0.59    inference(superposition,[],[f80,f52])).
% 1.76/0.59  fof(f52,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f22])).
% 1.76/0.59  fof(f22,plain,(
% 1.76/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.76/0.59    inference(ennf_transformation,[],[f7])).
% 1.76/0.59  fof(f7,axiom,(
% 1.76/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.76/0.59  fof(f80,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 1.76/0.59    inference(definition_unfolding,[],[f51,f71,f48])).
% 1.76/0.59  fof(f48,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.76/0.59    inference(cnf_transformation,[],[f4])).
% 1.76/0.59  fof(f4,axiom,(
% 1.76/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.76/0.59  fof(f51,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.76/0.59    inference(cnf_transformation,[],[f10])).
% 1.76/0.59  fof(f10,axiom,(
% 1.76/0.59    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.76/0.59  fof(f392,plain,(
% 1.76/0.59    ( ! [X15] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X15,X15)) )),
% 1.76/0.59    inference(forward_demodulation,[],[f391,f153])).
% 1.76/0.59  fof(f153,plain,(
% 1.76/0.59    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.76/0.59    inference(superposition,[],[f117,f77])).
% 1.76/0.59  fof(f77,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.76/0.59    inference(definition_unfolding,[],[f45,f71])).
% 1.76/0.59  fof(f45,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.76/0.59    inference(cnf_transformation,[],[f6])).
% 1.76/0.59  fof(f6,axiom,(
% 1.76/0.59    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.76/0.59  fof(f391,plain,(
% 1.76/0.59    ( ! [X15] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X15)) = k5_xboole_0(X15,X15)) )),
% 1.76/0.59    inference(subsumption_resolution,[],[f381,f83])).
% 1.76/0.59  fof(f83,plain,(
% 1.76/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.76/0.59    inference(equality_resolution,[],[f54])).
% 1.76/0.59  fof(f54,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.76/0.59    inference(cnf_transformation,[],[f30])).
% 1.76/0.59  fof(f30,plain,(
% 1.76/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.59    inference(flattening,[],[f29])).
% 1.76/0.59  fof(f29,plain,(
% 1.76/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.59    inference(nnf_transformation,[],[f3])).
% 1.76/0.59  fof(f3,axiom,(
% 1.76/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.76/0.59  fof(f381,plain,(
% 1.76/0.59    ( ! [X15] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X15)) = k5_xboole_0(X15,X15) | ~r1_tarski(X15,X15)) )),
% 1.76/0.59    inference(superposition,[],[f141,f117])).
% 1.76/0.59  fof(f141,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) )),
% 1.76/0.59    inference(superposition,[],[f78,f52])).
% 1.76/0.59  fof(f78,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.76/0.59    inference(definition_unfolding,[],[f49,f48,f48,f71])).
% 1.76/0.59  fof(f49,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f9])).
% 1.76/0.59  fof(f9,axiom,(
% 1.76/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.76/0.59  fof(f129,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) | ~r1_tarski(X0,X1)) )),
% 1.76/0.59    inference(superposition,[],[f79,f52])).
% 1.76/0.59  fof(f79,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.76/0.59    inference(definition_unfolding,[],[f50,f71,f48,f71])).
% 1.76/0.59  fof(f50,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f8])).
% 1.76/0.59  fof(f8,axiom,(
% 1.76/0.59    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.76/0.59  fof(f150,plain,(
% 1.76/0.59    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.76/0.59    inference(forward_demodulation,[],[f73,f76])).
% 1.76/0.59  fof(f73,plain,(
% 1.76/0.59    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))),
% 1.76/0.59    inference(definition_unfolding,[],[f40,f71,f72])).
% 1.76/0.59  fof(f40,plain,(
% 1.76/0.59    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.76/0.59    inference(cnf_transformation,[],[f28])).
% 1.76/0.59  fof(f28,plain,(
% 1.76/0.59    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 1.76/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27])).
% 1.76/0.59  fof(f27,plain,(
% 1.76/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 1.76/0.59    introduced(choice_axiom,[])).
% 1.76/0.59  fof(f21,plain,(
% 1.76/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.76/0.59    inference(ennf_transformation,[],[f20])).
% 1.76/0.59  fof(f20,negated_conjecture,(
% 1.76/0.59    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.76/0.59    inference(negated_conjecture,[],[f19])).
% 1.76/0.59  fof(f19,conjecture,(
% 1.76/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.76/0.59  fof(f39,plain,(
% 1.76/0.59    r2_hidden(sK1,sK2)),
% 1.76/0.59    inference(cnf_transformation,[],[f28])).
% 1.76/0.59  % SZS output end Proof for theBenchmark
% 1.76/0.59  % (5040)------------------------------
% 1.76/0.59  % (5040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (5040)Termination reason: Refutation
% 1.76/0.59  
% 1.76/0.59  % (5040)Memory used [KB]: 2174
% 1.76/0.59  % (5040)Time elapsed: 0.131 s
% 1.76/0.59  % (5040)------------------------------
% 1.76/0.59  % (5040)------------------------------
% 1.76/0.59  % (5010)Success in time 0.232 s
%------------------------------------------------------------------------------
