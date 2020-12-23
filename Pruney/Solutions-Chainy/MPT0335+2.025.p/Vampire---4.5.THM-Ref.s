%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:18 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   28 (  49 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 ( 148 expanded)
%              Number of equality atoms :   29 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(subsumption_resolution,[],[f224,f27])).

fof(f27,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f224,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f212,f173])).

fof(f173,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3)) ),
    inference(superposition,[],[f42,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f42,plain,(
    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f36,plain,(
    r1_tarski(k1_tarski(sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f26,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f212,plain,(
    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3)) ),
    inference(superposition,[],[f64,f25])).

fof(f25,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[],[f33,f41])).

fof(f41,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f24,f35])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (1405)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (1404)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (1429)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (1413)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (1406)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.53  % (1412)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.53  % (1401)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.53  % (1424)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.54  % (1410)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.54  % (1416)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.54  % (1402)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (1411)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.54  % (1430)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.54  % (1422)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.55  % (1412)Refutation found. Thanks to Tanya!
% 1.47/0.55  % SZS status Theorem for theBenchmark
% 1.47/0.55  % (1407)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.55  % (1428)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.55  % (1419)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.55  % (1418)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.55  % (1421)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.55  % (1417)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.55  % (1427)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.55  % (1409)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.56  % (1414)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.56  % (1403)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.47/0.56  % (1426)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.56  % (1408)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.56  % (1425)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f225,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(subsumption_resolution,[],[f224,f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f18])).
% 1.47/0.56  fof(f18,plain,(
% 1.47/0.56    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f17])).
% 1.47/0.56  fof(f17,plain,(
% 1.47/0.56    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f14,plain,(
% 1.47/0.56    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.47/0.56    inference(flattening,[],[f13])).
% 1.47/0.56  fof(f13,plain,(
% 1.47/0.56    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.47/0.56    inference(negated_conjecture,[],[f11])).
% 1.47/0.56  fof(f11,conjecture,(
% 1.47/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.47/0.56  fof(f224,plain,(
% 1.47/0.56    k1_tarski(sK3) = k3_xboole_0(sK0,sK2)),
% 1.47/0.56    inference(forward_demodulation,[],[f212,f173])).
% 1.47/0.56  fof(f173,plain,(
% 1.47/0.56    k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3))),
% 1.47/0.56    inference(superposition,[],[f42,f34])).
% 1.47/0.56  fof(f34,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f36,f35])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,plain,(
% 1.47/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f5])).
% 1.47/0.56  fof(f5,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.47/0.56  fof(f36,plain,(
% 1.47/0.56    r1_tarski(k1_tarski(sK3),sK0)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f26,f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.47/0.56    inference(nnf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    r2_hidden(sK3,sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f18])).
% 1.47/0.56  fof(f212,plain,(
% 1.47/0.56    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3))),
% 1.47/0.56    inference(superposition,[],[f64,f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f18])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) )),
% 1.47/0.56    inference(superposition,[],[f33,f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    sK0 = k3_xboole_0(sK0,sK1)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f24,f35])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    r1_tarski(sK0,sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f18])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (1412)------------------------------
% 1.47/0.56  % (1412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (1412)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (1412)Memory used [KB]: 10874
% 1.47/0.56  % (1412)Time elapsed: 0.133 s
% 1.47/0.56  % (1412)------------------------------
% 1.47/0.56  % (1412)------------------------------
% 1.47/0.56  % (1420)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.57  % (1400)Success in time 0.208 s
%------------------------------------------------------------------------------
