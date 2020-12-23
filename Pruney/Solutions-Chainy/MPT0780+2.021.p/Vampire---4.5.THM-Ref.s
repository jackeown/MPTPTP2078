%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:59 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   50 (  80 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :   92 ( 170 expanded)
%              Number of equality atoms :   47 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(backward_demodulation,[],[f163,f280])).

fof(f280,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f278,f49])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f278,plain,(
    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f230,f199])).

fof(f199,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(resolution,[],[f101,f45])).

fof(f45,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f97,f48])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f59,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f230,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(backward_demodulation,[],[f87,f229])).

fof(f229,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f228,f49])).

fof(f228,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f227,f53])).

fof(f53,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f227,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f219,f49])).

fof(f219,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f107,f47])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0)) ) ),
    inference(resolution,[],[f50,f47])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f87,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f163,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f46,f130])).

fof(f130,plain,(
    ! [X10,X9] : k2_wellord1(k2_wellord1(sK2,X9),X10) = k2_wellord1(sK2,k3_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f123,f114])).

fof(f114,plain,(
    ! [X10,X9] : k2_wellord1(k2_wellord1(sK2,X9),X10) = k2_wellord1(sK2,k3_xboole_0(X9,X10)) ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(f123,plain,(
    ! [X10,X9] : k2_wellord1(k2_wellord1(sK2,X9),X10) = k2_wellord1(k2_wellord1(sK2,X10),X9) ),
    inference(resolution,[],[f66,f44])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f46,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:16:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (23779)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (23782)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (23784)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (23787)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (23795)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (23785)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (23807)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (23780)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (23799)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (23792)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (23802)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (23790)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (23801)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (23794)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (23803)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (23808)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (23781)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (23788)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (23786)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (23783)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (23806)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (23797)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (23800)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (23805)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.56  % (23796)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.56  % (23793)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.48/0.56  % (23791)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.48/0.56  % (23789)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.48/0.56  % (23804)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.57  % (23786)Refutation found. Thanks to Tanya!
% 1.48/0.57  % SZS status Theorem for theBenchmark
% 1.48/0.57  % SZS output start Proof for theBenchmark
% 1.48/0.57  fof(f282,plain,(
% 1.48/0.57    $false),
% 1.48/0.57    inference(trivial_inequality_removal,[],[f281])).
% 1.48/0.57  fof(f281,plain,(
% 1.48/0.57    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)),
% 1.48/0.57    inference(backward_demodulation,[],[f163,f280])).
% 1.48/0.57  fof(f280,plain,(
% 1.48/0.57    sK0 = k3_xboole_0(sK0,sK1)),
% 1.48/0.57    inference(forward_demodulation,[],[f278,f49])).
% 1.48/0.57  fof(f49,plain,(
% 1.48/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f14])).
% 1.48/0.57  fof(f14,axiom,(
% 1.48/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.48/0.57  fof(f278,plain,(
% 1.48/0.57    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK0))),
% 1.48/0.57    inference(superposition,[],[f230,f199])).
% 1.48/0.57  fof(f199,plain,(
% 1.48/0.57    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.48/0.57    inference(resolution,[],[f101,f45])).
% 1.48/0.57  fof(f45,plain,(
% 1.48/0.57    r1_tarski(sK0,sK1)),
% 1.48/0.57    inference(cnf_transformation,[],[f41])).
% 1.48/0.57  fof(f41,plain,(
% 1.48/0.57    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f40])).
% 1.48/0.57  fof(f40,plain,(
% 1.48/0.57    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.48/0.57    introduced(choice_axiom,[])).
% 1.48/0.57  fof(f25,plain,(
% 1.48/0.57    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.48/0.57    inference(flattening,[],[f24])).
% 1.48/0.57  fof(f24,plain,(
% 1.48/0.57    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.48/0.57    inference(ennf_transformation,[],[f23])).
% 1.48/0.57  fof(f23,negated_conjecture,(
% 1.48/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.48/0.57    inference(negated_conjecture,[],[f22])).
% 1.48/0.57  fof(f22,conjecture,(
% 1.48/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).
% 1.48/0.57  fof(f101,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f97,f48])).
% 1.48/0.57  fof(f48,plain,(
% 1.48/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f14])).
% 1.48/0.57  fof(f97,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.48/0.57    inference(resolution,[],[f59,f47])).
% 1.48/0.57  fof(f47,plain,(
% 1.48/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f9])).
% 1.48/0.57  fof(f9,axiom,(
% 1.48/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.48/0.57  fof(f59,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.48/0.57    inference(cnf_transformation,[],[f33])).
% 1.48/0.57  fof(f33,plain,(
% 1.48/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.48/0.57    inference(flattening,[],[f32])).
% 1.48/0.57  fof(f32,plain,(
% 1.48/0.57    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f16])).
% 1.48/0.57  fof(f16,axiom,(
% 1.48/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.48/0.57  fof(f230,plain,(
% 1.48/0.57    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) )),
% 1.48/0.57    inference(backward_demodulation,[],[f87,f229])).
% 1.48/0.57  fof(f229,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f228,f49])).
% 1.48/0.57  fof(f228,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 1.48/0.57    inference(forward_demodulation,[],[f227,f53])).
% 1.48/0.57  fof(f53,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f17])).
% 1.48/0.57  fof(f17,axiom,(
% 1.48/0.57    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.48/0.57  fof(f227,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f219,f49])).
% 1.48/0.57  fof(f219,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))) )),
% 1.48/0.57    inference(resolution,[],[f107,f47])).
% 1.48/0.57  fof(f107,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0))) )),
% 1.48/0.57    inference(resolution,[],[f50,f47])).
% 1.48/0.57  fof(f50,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f26])).
% 1.48/0.57  fof(f26,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(ennf_transformation,[],[f13])).
% 1.48/0.57  fof(f13,axiom,(
% 1.48/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 1.48/0.57  fof(f87,plain,(
% 1.48/0.57    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 1.48/0.57    inference(resolution,[],[f57,f47])).
% 1.48/0.57  fof(f57,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f30])).
% 1.48/0.57  fof(f30,plain,(
% 1.48/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f12])).
% 1.48/0.57  fof(f12,axiom,(
% 1.48/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.48/0.57  fof(f163,plain,(
% 1.48/0.57    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 1.48/0.57    inference(superposition,[],[f46,f130])).
% 1.48/0.57  fof(f130,plain,(
% 1.48/0.57    ( ! [X10,X9] : (k2_wellord1(k2_wellord1(sK2,X9),X10) = k2_wellord1(sK2,k3_xboole_0(X10,X9))) )),
% 1.48/0.57    inference(forward_demodulation,[],[f123,f114])).
% 1.48/0.57  fof(f114,plain,(
% 1.48/0.57    ( ! [X10,X9] : (k2_wellord1(k2_wellord1(sK2,X9),X10) = k2_wellord1(sK2,k3_xboole_0(X9,X10))) )),
% 1.48/0.57    inference(resolution,[],[f65,f44])).
% 1.48/0.57  fof(f44,plain,(
% 1.48/0.57    v1_relat_1(sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f41])).
% 1.48/0.57  fof(f65,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f36])).
% 1.48/0.57  fof(f36,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.48/0.57    inference(ennf_transformation,[],[f20])).
% 1.48/0.57  fof(f20,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).
% 1.48/0.57  fof(f123,plain,(
% 1.48/0.57    ( ! [X10,X9] : (k2_wellord1(k2_wellord1(sK2,X9),X10) = k2_wellord1(k2_wellord1(sK2,X10),X9)) )),
% 1.48/0.57    inference(resolution,[],[f66,f44])).
% 1.48/0.57  fof(f66,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f37])).
% 1.48/0.57  fof(f37,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 1.48/0.57    inference(ennf_transformation,[],[f21])).
% 1.48/0.57  fof(f21,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 1.48/0.57  fof(f46,plain,(
% 1.48/0.57    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.48/0.57    inference(cnf_transformation,[],[f41])).
% 1.48/0.57  % SZS output end Proof for theBenchmark
% 1.48/0.57  % (23786)------------------------------
% 1.48/0.57  % (23786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (23786)Termination reason: Refutation
% 1.48/0.57  
% 1.48/0.57  % (23786)Memory used [KB]: 2046
% 1.48/0.57  % (23786)Time elapsed: 0.108 s
% 1.48/0.57  % (23786)------------------------------
% 1.48/0.57  % (23786)------------------------------
% 1.48/0.57  % (23798)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.58/0.58  % (23778)Success in time 0.213 s
%------------------------------------------------------------------------------
