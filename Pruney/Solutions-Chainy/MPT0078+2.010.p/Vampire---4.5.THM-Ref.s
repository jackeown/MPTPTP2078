%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:48 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 173 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   21
%              Number of atoms          :  115 ( 323 expanded)
%              Number of equality atoms :   68 ( 192 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1853,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1846,f27])).

fof(f27,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f1846,plain,(
    sK0 = sK2 ),
    inference(superposition,[],[f1842,f29])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1842,plain,(
    sK0 = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1841,f29])).

fof(f1841,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1834,f1368])).

fof(f1368,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f1353,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1353,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1216,f45])).

fof(f45,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f32,f24])).

fof(f24,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1216,plain,(
    ! [X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(sK1,X2)) ),
    inference(superposition,[],[f38,f1143])).

fof(f1143,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f64,f548])).

fof(f548,plain,(
    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f547,f29])).

fof(f547,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f546,f32])).

fof(f546,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f545,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f39,f29])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f545,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f469,f32])).

fof(f469,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK0),sK1)) ),
    inference(superposition,[],[f369,f59])).

fof(f59,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f57,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f369,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f43,f38])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f37,f34,f34])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f38,f29])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1834,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f40,f1806])).

fof(f1806,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f1449,f44])).

fof(f44,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f31,f24])).

fof(f1449,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f1239,f32])).

fof(f1239,plain,(
    ! [X2] : k4_xboole_0(sK2,k2_xboole_0(sK1,X2)) = k4_xboole_0(sK2,X2) ),
    inference(superposition,[],[f38,f1153])).

fof(f1153,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f64,f556])).

fof(f556,plain,(
    sK2 = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f555,f29])).

fof(f555,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f554,f32])).

fof(f554,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f553,f52])).

fof(f553,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK2))) ),
    inference(forward_demodulation,[],[f471,f32])).

fof(f471,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK2),sK1)) ),
    inference(superposition,[],[f369,f60])).

fof(f60,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f58,f30])).

fof(f58,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f41,f26])).

fof(f26,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.56  % (1421)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (1411)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (1413)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.57  % (1416)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (1418)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (1426)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (1415)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.58  % (1437)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.59  % (1410)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.45/0.59  % (1414)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.59  % (1412)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.59  % (1433)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.60  % (1425)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.60  % (1425)Refutation not found, incomplete strategy% (1425)------------------------------
% 1.45/0.60  % (1425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.60  % (1425)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.60  
% 1.45/0.60  % (1425)Memory used [KB]: 6140
% 1.45/0.60  % (1425)Time elapsed: 0.002 s
% 1.45/0.60  % (1425)------------------------------
% 1.45/0.60  % (1425)------------------------------
% 1.45/0.60  % (1439)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.83/0.60  % (1422)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.83/0.60  % (1424)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.83/0.61  % (1432)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.83/0.61  % (1420)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.83/0.61  % (1417)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.83/0.62  % (1429)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.83/0.62  % (1431)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.83/0.62  % (1438)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.83/0.62  % (1423)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.83/0.63  % (1430)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.83/0.63  % (1436)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.83/0.63  % (1428)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.83/0.63  % (1435)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.83/0.63  % (1420)Refutation not found, incomplete strategy% (1420)------------------------------
% 1.83/0.63  % (1420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.63  % (1420)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.63  
% 1.83/0.63  % (1420)Memory used [KB]: 10618
% 1.83/0.63  % (1420)Time elapsed: 0.200 s
% 1.83/0.63  % (1420)------------------------------
% 1.83/0.63  % (1420)------------------------------
% 1.83/0.64  % (1419)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.83/0.64  % (1427)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.83/0.64  % (1427)Refutation not found, incomplete strategy% (1427)------------------------------
% 1.83/0.64  % (1427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.64  % (1427)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.64  
% 1.83/0.64  % (1427)Memory used [KB]: 10618
% 1.83/0.64  % (1427)Time elapsed: 0.208 s
% 1.83/0.64  % (1427)------------------------------
% 1.83/0.64  % (1427)------------------------------
% 1.83/0.64  % (1434)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.27/0.73  % (1413)Refutation found. Thanks to Tanya!
% 2.27/0.73  % SZS status Theorem for theBenchmark
% 2.27/0.74  % SZS output start Proof for theBenchmark
% 2.27/0.74  fof(f1853,plain,(
% 2.27/0.74    $false),
% 2.27/0.74    inference(subsumption_resolution,[],[f1846,f27])).
% 2.27/0.74  fof(f27,plain,(
% 2.27/0.74    sK0 != sK2),
% 2.27/0.74    inference(cnf_transformation,[],[f19])).
% 2.27/0.74  fof(f19,plain,(
% 2.27/0.74    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 2.27/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 2.27/0.74  fof(f18,plain,(
% 2.27/0.74    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 2.27/0.74    introduced(choice_axiom,[])).
% 2.27/0.74  fof(f15,plain,(
% 2.27/0.74    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 2.27/0.74    inference(flattening,[],[f14])).
% 2.27/0.74  fof(f14,plain,(
% 2.27/0.74    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 2.27/0.74    inference(ennf_transformation,[],[f12])).
% 2.27/0.74  fof(f12,negated_conjecture,(
% 2.27/0.74    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 2.27/0.74    inference(negated_conjecture,[],[f11])).
% 2.27/0.74  fof(f11,conjecture,(
% 2.27/0.74    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 2.27/0.74  fof(f1846,plain,(
% 2.27/0.74    sK0 = sK2),
% 2.27/0.74    inference(superposition,[],[f1842,f29])).
% 2.27/0.74  fof(f29,plain,(
% 2.27/0.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.27/0.74    inference(cnf_transformation,[],[f6])).
% 2.27/0.74  fof(f6,axiom,(
% 2.27/0.74    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.27/0.74  fof(f1842,plain,(
% 2.27/0.74    sK0 = k4_xboole_0(sK2,k1_xboole_0)),
% 2.27/0.74    inference(forward_demodulation,[],[f1841,f29])).
% 2.27/0.74  fof(f1841,plain,(
% 2.27/0.74    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.27/0.74    inference(forward_demodulation,[],[f1834,f1368])).
% 2.27/0.74  fof(f1368,plain,(
% 2.27/0.74    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 2.27/0.74    inference(forward_demodulation,[],[f1353,f31])).
% 2.27/0.74  fof(f31,plain,(
% 2.27/0.74    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.27/0.74    inference(cnf_transformation,[],[f8])).
% 2.27/0.74  fof(f8,axiom,(
% 2.27/0.74    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.27/0.74  fof(f1353,plain,(
% 2.27/0.74    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 2.27/0.74    inference(superposition,[],[f1216,f45])).
% 2.27/0.74  fof(f45,plain,(
% 2.27/0.74    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)),
% 2.27/0.74    inference(superposition,[],[f32,f24])).
% 2.27/0.74  fof(f24,plain,(
% 2.27/0.74    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 2.27/0.74    inference(cnf_transformation,[],[f19])).
% 2.27/0.74  fof(f32,plain,(
% 2.27/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.27/0.74    inference(cnf_transformation,[],[f1])).
% 2.27/0.74  fof(f1,axiom,(
% 2.27/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.27/0.74  fof(f1216,plain,(
% 2.27/0.74    ( ! [X2] : (k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(sK1,X2))) )),
% 2.27/0.74    inference(superposition,[],[f38,f1143])).
% 2.27/0.74  fof(f1143,plain,(
% 2.27/0.74    sK0 = k4_xboole_0(sK0,sK1)),
% 2.27/0.74    inference(superposition,[],[f64,f548])).
% 2.27/0.74  fof(f548,plain,(
% 2.27/0.74    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1))),
% 2.27/0.74    inference(forward_demodulation,[],[f547,f29])).
% 2.27/0.74  fof(f547,plain,(
% 2.27/0.74    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1))),
% 2.27/0.74    inference(forward_demodulation,[],[f546,f32])).
% 2.27/0.74  fof(f546,plain,(
% 2.27/0.74    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0))),
% 2.27/0.74    inference(forward_demodulation,[],[f545,f52])).
% 2.27/0.74  fof(f52,plain,(
% 2.27/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.27/0.74    inference(forward_demodulation,[],[f39,f29])).
% 2.27/0.74  fof(f39,plain,(
% 2.27/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.27/0.74    inference(definition_unfolding,[],[f28,f34])).
% 2.27/0.74  fof(f34,plain,(
% 2.27/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.27/0.74    inference(cnf_transformation,[],[f9])).
% 2.27/0.74  fof(f9,axiom,(
% 2.27/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.27/0.74  fof(f28,plain,(
% 2.27/0.74    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.27/0.74    inference(cnf_transformation,[],[f5])).
% 2.27/0.74  fof(f5,axiom,(
% 2.27/0.74    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.27/0.74  fof(f545,plain,(
% 2.27/0.74    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK0)))),
% 2.27/0.74    inference(forward_demodulation,[],[f469,f32])).
% 2.27/0.74  fof(f469,plain,(
% 2.27/0.74    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK0),sK1))),
% 2.27/0.74    inference(superposition,[],[f369,f59])).
% 2.27/0.74  fof(f59,plain,(
% 2.27/0.74    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.27/0.74    inference(resolution,[],[f57,f30])).
% 2.27/0.74  fof(f30,plain,(
% 2.27/0.74    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.27/0.74    inference(cnf_transformation,[],[f21])).
% 2.27/0.74  fof(f21,plain,(
% 2.27/0.74    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.27/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f20])).
% 2.27/0.74  fof(f20,plain,(
% 2.27/0.74    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.27/0.74    introduced(choice_axiom,[])).
% 2.27/0.74  fof(f16,plain,(
% 2.27/0.74    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.27/0.74    inference(ennf_transformation,[],[f4])).
% 2.27/0.74  fof(f4,axiom,(
% 2.27/0.74    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.27/0.74  fof(f57,plain,(
% 2.27/0.74    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 2.27/0.74    inference(resolution,[],[f41,f25])).
% 2.27/0.74  fof(f25,plain,(
% 2.27/0.74    r1_xboole_0(sK0,sK1)),
% 2.27/0.74    inference(cnf_transformation,[],[f19])).
% 2.27/0.74  fof(f41,plain,(
% 2.27/0.74    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.27/0.74    inference(definition_unfolding,[],[f36,f34])).
% 2.27/0.74  fof(f36,plain,(
% 2.27/0.74    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.27/0.74    inference(cnf_transformation,[],[f23])).
% 2.27/0.74  fof(f23,plain,(
% 2.27/0.74    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.27/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f22])).
% 2.27/0.74  fof(f22,plain,(
% 2.27/0.74    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.27/0.74    introduced(choice_axiom,[])).
% 2.27/0.74  fof(f17,plain,(
% 2.27/0.74    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.27/0.74    inference(ennf_transformation,[],[f13])).
% 2.27/0.74  fof(f13,plain,(
% 2.27/0.74    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.27/0.74    inference(rectify,[],[f3])).
% 2.27/0.74  fof(f3,axiom,(
% 2.27/0.74    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.27/0.74  fof(f369,plain,(
% 2.27/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 2.27/0.74    inference(forward_demodulation,[],[f43,f38])).
% 2.27/0.74  fof(f43,plain,(
% 2.27/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.27/0.74    inference(definition_unfolding,[],[f37,f34,f34])).
% 2.27/0.74  fof(f37,plain,(
% 2.27/0.74    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.27/0.74    inference(cnf_transformation,[],[f10])).
% 2.27/0.74  fof(f10,axiom,(
% 2.27/0.74    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.27/0.74  fof(f64,plain,(
% 2.27/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 2.27/0.74    inference(superposition,[],[f38,f29])).
% 2.27/0.74  fof(f38,plain,(
% 2.27/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.27/0.74    inference(cnf_transformation,[],[f7])).
% 2.27/0.74  fof(f7,axiom,(
% 2.27/0.74    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.27/0.74  fof(f1834,plain,(
% 2.27/0.74    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.27/0.74    inference(superposition,[],[f40,f1806])).
% 2.27/0.74  fof(f1806,plain,(
% 2.27/0.74    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 2.27/0.74    inference(superposition,[],[f1449,f44])).
% 2.27/0.74  fof(f44,plain,(
% 2.27/0.74    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.27/0.74    inference(superposition,[],[f31,f24])).
% 2.27/0.74  fof(f1449,plain,(
% 2.27/0.74    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK1))) )),
% 2.27/0.74    inference(superposition,[],[f1239,f32])).
% 2.27/0.74  fof(f1239,plain,(
% 2.27/0.74    ( ! [X2] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X2)) = k4_xboole_0(sK2,X2)) )),
% 2.27/0.74    inference(superposition,[],[f38,f1153])).
% 2.27/0.74  fof(f1153,plain,(
% 2.27/0.74    sK2 = k4_xboole_0(sK2,sK1)),
% 2.27/0.74    inference(superposition,[],[f64,f556])).
% 2.27/0.74  fof(f556,plain,(
% 2.27/0.74    sK2 = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK1))),
% 2.27/0.74    inference(forward_demodulation,[],[f555,f29])).
% 2.27/0.74  fof(f555,plain,(
% 2.27/0.74    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK1))),
% 2.27/0.74    inference(forward_demodulation,[],[f554,f32])).
% 2.27/0.74  fof(f554,plain,(
% 2.27/0.74    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(sK1,k1_xboole_0))),
% 2.27/0.74    inference(forward_demodulation,[],[f553,f52])).
% 2.27/0.74  fof(f553,plain,(
% 2.27/0.74    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK2)))),
% 2.27/0.74    inference(forward_demodulation,[],[f471,f32])).
% 2.27/0.74  fof(f471,plain,(
% 2.27/0.74    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK2),sK1))),
% 2.27/0.74    inference(superposition,[],[f369,f60])).
% 2.27/0.74  fof(f60,plain,(
% 2.27/0.74    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 2.27/0.74    inference(resolution,[],[f58,f30])).
% 2.27/0.74  fof(f58,plain,(
% 2.27/0.74    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) )),
% 2.27/0.74    inference(resolution,[],[f41,f26])).
% 2.27/0.74  fof(f26,plain,(
% 2.27/0.74    r1_xboole_0(sK2,sK1)),
% 2.27/0.74    inference(cnf_transformation,[],[f19])).
% 2.27/0.74  fof(f40,plain,(
% 2.27/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.27/0.74    inference(definition_unfolding,[],[f33,f34,f34])).
% 2.27/0.74  fof(f33,plain,(
% 2.27/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.27/0.74    inference(cnf_transformation,[],[f2])).
% 2.27/0.74  fof(f2,axiom,(
% 2.27/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.27/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.27/0.74  % SZS output end Proof for theBenchmark
% 2.27/0.74  % (1413)------------------------------
% 2.27/0.74  % (1413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.74  % (1413)Termination reason: Refutation
% 2.27/0.74  
% 2.27/0.74  % (1413)Memory used [KB]: 12281
% 2.27/0.74  % (1413)Time elapsed: 0.275 s
% 2.27/0.74  % (1413)------------------------------
% 2.27/0.74  % (1413)------------------------------
% 2.27/0.74  % (1409)Success in time 0.374 s
%------------------------------------------------------------------------------
