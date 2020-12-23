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

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 100 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 220 expanded)
%              Number of equality atoms :   46 ( 129 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1912,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1895,f31])).

fof(f31,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f1895,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f1802,f292])).

fof(f292,plain,(
    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3)) ),
    inference(superposition,[],[f96,f29])).

fof(f29,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[],[f36,f45])).

fof(f45,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1802,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3)) ),
    inference(superposition,[],[f1789,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1789,plain,(
    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0) ),
    inference(forward_demodulation,[],[f1745,f242])).

fof(f242,plain,(
    ! [X1] : k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),k2_xboole_0(sK2,X1)) ),
    inference(forward_demodulation,[],[f239,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f239,plain,(
    ! [X1] : k2_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),X1)) = k3_xboole_0(k1_tarski(sK3),k2_xboole_0(sK2,X1)) ),
    inference(superposition,[],[f42,f135])).

fof(f135,plain,(
    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2) ),
    inference(forward_demodulation,[],[f126,f29])).

fof(f126,plain,(
    k3_xboole_0(sK1,sK2) = k3_xboole_0(k1_tarski(sK3),sK2) ),
    inference(superposition,[],[f57,f38])).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f57,plain,(
    ! [X0] : k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_tarski(sK3),X0) ),
    inference(superposition,[],[f36,f29])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f1745,plain,(
    k3_xboole_0(k1_tarski(sK3),sK0) = k3_xboole_0(k1_tarski(sK3),k2_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f191,f523])).

fof(f523,plain,(
    sK0 = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f514,f49])).

fof(f49,plain,(
    sK0 = k2_xboole_0(k1_tarski(sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f30,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f514,plain,(
    k2_xboole_0(k1_tarski(sK3),sK0) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f141,f45])).

fof(f141,plain,(
    ! [X2] : k3_xboole_0(sK1,k2_xboole_0(sK2,X2)) = k2_xboole_0(k1_tarski(sK3),k3_xboole_0(X2,sK1)) ),
    inference(superposition,[],[f60,f37])).

fof(f60,plain,(
    ! [X1] : k3_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f42,f29])).

fof(f191,plain,(
    ! [X0] : k3_xboole_0(k1_tarski(sK3),X0) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f36,f74])).

fof(f74,plain,(
    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f59,f39])).

fof(f59,plain,(
    r1_tarski(k1_tarski(sK3),sK1) ),
    inference(superposition,[],[f41,f29])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (28508)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.50  % (28489)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (28497)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (28494)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (28488)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.53  % (28490)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (28503)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.53  % (28505)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.53  % (28514)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.53  % (28504)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.54  % (28492)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.54  % (28499)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.54  % (28493)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.54  % (28491)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.43/0.54  % (28501)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.54  % (28517)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.54  % (28513)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.54  % (28519)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.55  % (28516)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.55  % (28498)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (28510)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.55  % (28507)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.55  % (28500)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.55  % (28496)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.55  % (28515)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.55  % (28512)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.55  % (28495)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.56  % (28509)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.56  % (28506)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.56  % (28518)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.59  % (28497)Refutation found. Thanks to Tanya!
% 1.43/0.59  % SZS status Theorem for theBenchmark
% 1.43/0.59  % SZS output start Proof for theBenchmark
% 1.43/0.59  fof(f1912,plain,(
% 1.43/0.59    $false),
% 1.43/0.59    inference(subsumption_resolution,[],[f1895,f31])).
% 1.43/0.59  fof(f31,plain,(
% 1.43/0.59    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.43/0.59    inference(cnf_transformation,[],[f23])).
% 1.43/0.59  fof(f23,plain,(
% 1.43/0.59    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.43/0.59    inference(flattening,[],[f22])).
% 1.43/0.59  fof(f22,plain,(
% 1.43/0.59    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.43/0.59    inference(ennf_transformation,[],[f20])).
% 1.43/0.59  fof(f20,negated_conjecture,(
% 1.43/0.59    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 1.43/0.59    inference(negated_conjecture,[],[f19])).
% 1.43/0.59  fof(f19,conjecture,(
% 1.43/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 1.43/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.43/0.59  fof(f1895,plain,(
% 1.43/0.59    k1_tarski(sK3) = k3_xboole_0(sK0,sK2)),
% 1.43/0.59    inference(superposition,[],[f1802,f292])).
% 1.43/0.59  fof(f292,plain,(
% 1.43/0.59    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3))),
% 1.43/0.59    inference(superposition,[],[f96,f29])).
% 1.43/0.59  fof(f29,plain,(
% 1.43/0.59    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 1.43/0.59    inference(cnf_transformation,[],[f23])).
% 1.43/0.59  fof(f96,plain,(
% 1.43/0.59    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) )),
% 1.43/0.59    inference(superposition,[],[f36,f45])).
% 1.43/0.59  fof(f45,plain,(
% 1.43/0.59    sK0 = k3_xboole_0(sK0,sK1)),
% 1.43/0.59    inference(unit_resulting_resolution,[],[f28,f39])).
% 1.43/0.59  fof(f39,plain,(
% 1.43/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.43/0.59    inference(cnf_transformation,[],[f26])).
% 1.43/0.59  fof(f26,plain,(
% 1.43/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.43/0.59    inference(ennf_transformation,[],[f11])).
% 1.43/0.59  fof(f11,axiom,(
% 1.43/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.43/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.43/0.59  fof(f28,plain,(
% 1.43/0.59    r1_tarski(sK0,sK1)),
% 1.43/0.59    inference(cnf_transformation,[],[f23])).
% 1.43/0.59  fof(f36,plain,(
% 1.43/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.43/0.59    inference(cnf_transformation,[],[f6])).
% 1.43/0.59  fof(f6,axiom,(
% 1.43/0.59    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.43/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.43/0.59  fof(f1802,plain,(
% 1.43/0.59    k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3))),
% 1.43/0.59    inference(superposition,[],[f1789,f37])).
% 1.43/0.59  fof(f37,plain,(
% 1.43/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.43/0.59    inference(cnf_transformation,[],[f1])).
% 1.43/0.59  fof(f1,axiom,(
% 1.43/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.43/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.43/0.59  fof(f1789,plain,(
% 1.43/0.59    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0)),
% 1.43/0.59    inference(forward_demodulation,[],[f1745,f242])).
% 1.43/0.59  fof(f242,plain,(
% 1.43/0.59    ( ! [X1] : (k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),k2_xboole_0(sK2,X1))) )),
% 1.43/0.59    inference(forward_demodulation,[],[f239,f43])).
% 1.43/0.59  fof(f43,plain,(
% 1.43/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.43/0.59    inference(cnf_transformation,[],[f9])).
% 1.43/0.59  fof(f9,axiom,(
% 1.43/0.59    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.43/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.43/0.59  fof(f239,plain,(
% 1.43/0.59    ( ! [X1] : (k2_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),X1)) = k3_xboole_0(k1_tarski(sK3),k2_xboole_0(sK2,X1))) )),
% 1.43/0.59    inference(superposition,[],[f42,f135])).
% 1.43/0.59  fof(f135,plain,(
% 1.43/0.59    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2)),
% 1.43/0.59    inference(forward_demodulation,[],[f126,f29])).
% 1.43/0.59  fof(f126,plain,(
% 1.43/0.59    k3_xboole_0(sK1,sK2) = k3_xboole_0(k1_tarski(sK3),sK2)),
% 1.43/0.59    inference(superposition,[],[f57,f38])).
% 1.43/0.59  fof(f38,plain,(
% 1.43/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.43/0.59    inference(cnf_transformation,[],[f21])).
% 1.43/0.59  fof(f21,plain,(
% 1.43/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.43/0.59    inference(rectify,[],[f4])).
% 1.43/0.59  fof(f4,axiom,(
% 1.43/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.43/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.43/0.59  fof(f57,plain,(
% 1.43/0.59    ( ! [X0] : (k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_tarski(sK3),X0)) )),
% 1.43/0.59    inference(superposition,[],[f36,f29])).
% 1.43/0.59  fof(f42,plain,(
% 1.43/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.43/0.59    inference(cnf_transformation,[],[f10])).
% 1.43/0.59  fof(f10,axiom,(
% 1.43/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.43/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 1.43/0.59  fof(f1745,plain,(
% 1.43/0.59    k3_xboole_0(k1_tarski(sK3),sK0) = k3_xboole_0(k1_tarski(sK3),k2_xboole_0(sK2,sK0))),
% 1.43/0.59    inference(superposition,[],[f191,f523])).
% 1.43/0.59  fof(f523,plain,(
% 1.43/0.59    sK0 = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 1.43/0.59    inference(forward_demodulation,[],[f514,f49])).
% 1.43/0.59  fof(f49,plain,(
% 1.43/0.59    sK0 = k2_xboole_0(k1_tarski(sK3),sK0)),
% 1.43/0.59    inference(unit_resulting_resolution,[],[f30,f35])).
% 1.43/0.59  fof(f35,plain,(
% 1.43/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.43/0.59    inference(cnf_transformation,[],[f25])).
% 1.43/0.59  fof(f25,plain,(
% 1.43/0.59    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.43/0.59    inference(ennf_transformation,[],[f18])).
% 1.43/0.59  fof(f18,axiom,(
% 1.43/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.43/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.43/0.59  fof(f30,plain,(
% 1.43/0.59    r2_hidden(sK3,sK0)),
% 1.43/0.59    inference(cnf_transformation,[],[f23])).
% 1.43/0.59  fof(f514,plain,(
% 1.43/0.59    k2_xboole_0(k1_tarski(sK3),sK0) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 1.43/0.59    inference(superposition,[],[f141,f45])).
% 1.43/0.59  fof(f141,plain,(
% 1.43/0.59    ( ! [X2] : (k3_xboole_0(sK1,k2_xboole_0(sK2,X2)) = k2_xboole_0(k1_tarski(sK3),k3_xboole_0(X2,sK1))) )),
% 1.43/0.59    inference(superposition,[],[f60,f37])).
% 1.43/0.59  fof(f60,plain,(
% 1.43/0.59    ( ! [X1] : (k3_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,X1))) )),
% 1.43/0.59    inference(superposition,[],[f42,f29])).
% 1.43/0.59  fof(f191,plain,(
% 1.43/0.59    ( ! [X0] : (k3_xboole_0(k1_tarski(sK3),X0) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,X0))) )),
% 1.43/0.59    inference(superposition,[],[f36,f74])).
% 1.43/0.59  fof(f74,plain,(
% 1.43/0.59    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK1)),
% 1.43/0.59    inference(unit_resulting_resolution,[],[f59,f39])).
% 1.43/0.59  fof(f59,plain,(
% 1.43/0.59    r1_tarski(k1_tarski(sK3),sK1)),
% 1.43/0.59    inference(superposition,[],[f41,f29])).
% 1.43/0.59  fof(f41,plain,(
% 1.43/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.43/0.59    inference(cnf_transformation,[],[f7])).
% 1.43/0.60  fof(f7,axiom,(
% 1.43/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.43/0.60  % SZS output end Proof for theBenchmark
% 1.43/0.60  % (28497)------------------------------
% 1.43/0.60  % (28497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.60  % (28497)Termination reason: Refutation
% 1.43/0.60  
% 1.43/0.60  % (28497)Memory used [KB]: 11769
% 1.43/0.60  % (28497)Time elapsed: 0.167 s
% 1.43/0.60  % (28497)------------------------------
% 1.43/0.60  % (28497)------------------------------
% 1.43/0.60  % (28484)Success in time 0.233 s
%------------------------------------------------------------------------------
