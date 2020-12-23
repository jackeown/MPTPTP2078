%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 130 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  114 ( 318 expanded)
%              Number of equality atoms :   53 ( 161 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1007,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1006,f314])).

fof(f314,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k1_tarski(sK3)) ),
    inference(unit_resulting_resolution,[],[f27,f236,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f236,plain,(
    r1_tarski(k1_tarski(sK3),k3_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f215,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f215,plain,(
    r1_tarski(k1_tarski(sK3),sK0) ),
    inference(superposition,[],[f36,f68])).

fof(f68,plain,(
    sK0 = k2_xboole_0(k1_tarski(sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f26,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f26,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f20])).

fof(f20,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f46,plain,(
    r1_tarski(k1_tarski(sK3),sK2) ),
    inference(superposition,[],[f44,f25])).

fof(f25,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f35,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f27,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f1006,plain,(
    r1_tarski(k3_xboole_0(sK0,sK2),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f992,f29])).

fof(f992,plain,(
    r1_tarski(k3_xboole_0(sK2,sK0),k1_tarski(sK3)) ),
    inference(superposition,[],[f946,f634])).

fof(f634,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f633,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f40,f29])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f633,plain,(
    k3_xboole_0(sK2,sK1) = k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,k1_tarski(sK3))) ),
    inference(forward_demodulation,[],[f632,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f632,plain,(
    k3_xboole_0(sK2,sK1) = k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3))) ),
    inference(forward_demodulation,[],[f631,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f631,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3))) = k3_xboole_0(sK2,k3_xboole_0(sK1,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f630,f29])).

fof(f630,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3))) = k3_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)) ),
    inference(forward_demodulation,[],[f629,f63])).

fof(f63,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f43,f34])).

fof(f43,plain,(
    r1_tarski(k1_tarski(sK3),sK1) ),
    inference(superposition,[],[f35,f25])).

fof(f629,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3))) = k3_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k1_tarski(sK3),sK1))) ),
    inference(forward_demodulation,[],[f620,f29])).

fof(f620,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3))) = k3_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k1_tarski(sK3),sK1),k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f173,f550])).

fof(f550,plain,(
    sK2 = k2_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(superposition,[],[f52,f25])).

fof(f173,plain,(
    ! [X0] : k3_xboole_0(k2_xboole_0(sK2,X0),k3_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(sK1,sK2))) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,sK1),k1_tarski(sK3)),k3_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f157,f25])).

fof(f157,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k2_xboole_0(X2,X0),k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f37,f29])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).

fof(f946,plain,(
    ! [X29] : r1_tarski(k3_xboole_0(X29,sK0),k3_xboole_0(X29,sK1)) ),
    inference(superposition,[],[f151,f65])).

fof(f65,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f24,f34])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f151,plain,(
    ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X3,X4),k3_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f36,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:42:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (16121)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (16111)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (16131)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (16110)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (16112)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (16113)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (16122)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (16125)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.50  % (16120)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (16127)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (16126)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (16114)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (16133)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (16128)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (16118)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (16117)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (16108)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (16119)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (16129)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (16109)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (16130)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (16115)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.55  % (16132)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (16124)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (16123)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.56  % (16116)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.57  % (16108)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1007,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f1006,f314])).
% 0.21/0.57  fof(f314,plain,(
% 0.21/0.57    ~r1_tarski(k3_xboole_0(sK0,sK2),k1_tarski(sK3))),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f27,f236,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f236,plain,(
% 0.21/0.57    r1_tarski(k1_tarski(sK3),k3_xboole_0(sK0,sK2))),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f46,f215,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.57  fof(f215,plain,(
% 0.21/0.57    r1_tarski(k1_tarski(sK3),sK0)),
% 0.21/0.57    inference(superposition,[],[f36,f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    sK0 = k2_xboole_0(k1_tarski(sK3),sK0)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f26,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    r2_hidden(sK3,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 0.21/0.57    inference(negated_conjecture,[],[f12])).
% 0.21/0.57  fof(f12,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    r1_tarski(k1_tarski(sK3),sK2)),
% 0.21/0.57    inference(superposition,[],[f44,f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.21/0.57    inference(superposition,[],[f35,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f1006,plain,(
% 0.21/0.57    r1_tarski(k3_xboole_0(sK0,sK2),k1_tarski(sK3))),
% 0.21/0.57    inference(forward_demodulation,[],[f992,f29])).
% 0.21/0.57  fof(f992,plain,(
% 0.21/0.57    r1_tarski(k3_xboole_0(sK2,sK0),k1_tarski(sK3))),
% 0.21/0.57    inference(superposition,[],[f946,f634])).
% 0.21/0.57  fof(f634,plain,(
% 0.21/0.57    k1_tarski(sK3) = k3_xboole_0(sK2,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f633,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 0.21/0.57    inference(superposition,[],[f40,f29])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.57  fof(f633,plain,(
% 0.21/0.57    k3_xboole_0(sK2,sK1) = k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,k1_tarski(sK3)))),
% 0.21/0.57    inference(forward_demodulation,[],[f632,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f35,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.57  fof(f632,plain,(
% 0.21/0.57    k3_xboole_0(sK2,sK1) = k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3)))),
% 0.21/0.57    inference(forward_demodulation,[],[f631,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.57  fof(f631,plain,(
% 0.21/0.57    k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3))) = k3_xboole_0(sK2,k3_xboole_0(sK1,k2_xboole_0(sK1,sK2)))),
% 0.21/0.57    inference(forward_demodulation,[],[f630,f29])).
% 0.21/0.57  fof(f630,plain,(
% 0.21/0.57    k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3))) = k3_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))),
% 0.21/0.57    inference(forward_demodulation,[],[f629,f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(k1_tarski(sK3),sK1)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f43,f34])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    r1_tarski(k1_tarski(sK3),sK1)),
% 0.21/0.57    inference(superposition,[],[f35,f25])).
% 0.21/0.57  fof(f629,plain,(
% 0.21/0.57    k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3))) = k3_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k1_tarski(sK3),sK1)))),
% 0.21/0.57    inference(forward_demodulation,[],[f620,f29])).
% 0.21/0.57  fof(f620,plain,(
% 0.21/0.57    k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)),k3_xboole_0(sK2,k1_tarski(sK3))) = k3_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k1_tarski(sK3),sK1),k2_xboole_0(sK1,sK2)))),
% 0.21/0.57    inference(superposition,[],[f173,f550])).
% 0.21/0.57  fof(f550,plain,(
% 0.21/0.57    sK2 = k2_xboole_0(sK2,k1_tarski(sK3))),
% 0.21/0.57    inference(superposition,[],[f52,f25])).
% 0.21/0.57  fof(f173,plain,(
% 0.21/0.57    ( ! [X0] : (k3_xboole_0(k2_xboole_0(sK2,X0),k3_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(sK1,sK2))) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,sK1),k1_tarski(sK3)),k3_xboole_0(sK2,X0))) )),
% 0.21/0.57    inference(superposition,[],[f157,f25])).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k2_xboole_0(X2,X0),k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f37,f29])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).
% 0.21/0.57  fof(f946,plain,(
% 0.21/0.57    ( ! [X29] : (r1_tarski(k3_xboole_0(X29,sK0),k3_xboole_0(X29,sK1))) )),
% 0.21/0.57    inference(superposition,[],[f151,f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f24,f34])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    r1_tarski(sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f151,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X3,X4),k3_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 0.21/0.57    inference(superposition,[],[f36,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (16108)------------------------------
% 0.21/0.57  % (16108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (16108)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (16108)Memory used [KB]: 11257
% 0.21/0.57  % (16108)Time elapsed: 0.138 s
% 0.21/0.57  % (16108)------------------------------
% 0.21/0.57  % (16108)------------------------------
% 0.21/0.58  % (16107)Success in time 0.219 s
%------------------------------------------------------------------------------
