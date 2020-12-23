%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  84 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 178 expanded)
%              Number of equality atoms :   47 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(backward_demodulation,[],[f119,f191])).

fof(f191,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f190,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f190,plain,(
    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f162,f146])).

fof(f146,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(resolution,[],[f90,f44])).

fof(f44,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f39])).

fof(f39,plain,
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f88,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f57,f46])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f162,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(backward_demodulation,[],[f82,f161])).

fof(f161,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(forward_demodulation,[],[f160,f48])).

fof(f160,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X2),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f159,f52])).

fof(f52,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f159,plain,(
    ! [X2,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(forward_demodulation,[],[f155,f48])).

fof(f155,plain,(
    ! [X2,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),k2_relat_1(k6_relat_1(X1))) ),
    inference(resolution,[],[f98,f46])).

fof(f98,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),k2_relat_1(X1)) ) ),
    inference(resolution,[],[f49,f46])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f82,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f55,f46])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f119,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f45,f106])).

fof(f106,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f103,f100])).

fof(f100,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f63,f43])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(f103,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0) ),
    inference(resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(f45,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:02:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (32215)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (32215)Refutation not found, incomplete strategy% (32215)------------------------------
% 0.21/0.54  % (32215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32215)Memory used [KB]: 1663
% 0.21/0.54  % (32215)Time elapsed: 0.112 s
% 0.21/0.54  % (32215)------------------------------
% 0.21/0.54  % (32215)------------------------------
% 0.21/0.54  % (32217)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (32232)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (32222)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (32238)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (32220)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (32214)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.59  % (32218)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.60  % (32228)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.60  % (32219)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.60  % (32221)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.60  % (32237)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.60  % (32227)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.60  % (32234)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.61  % (32224)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.61  % (32235)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.61  % (32225)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.61  % (32223)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.61  % (32240)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.61  % (32231)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.61  % (32241)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.62  % (32229)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.62  % (32239)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.62  % (32226)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.62  % (32243)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.62  % (32230)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.63  % (32216)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.63  % (32221)Refutation found. Thanks to Tanya!
% 0.21/0.63  % SZS status Theorem for theBenchmark
% 0.21/0.63  % SZS output start Proof for theBenchmark
% 0.21/0.63  fof(f193,plain,(
% 0.21/0.63    $false),
% 0.21/0.63    inference(trivial_inequality_removal,[],[f192])).
% 0.21/0.63  fof(f192,plain,(
% 0.21/0.63    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)),
% 0.21/0.63    inference(backward_demodulation,[],[f119,f191])).
% 0.21/0.63  fof(f191,plain,(
% 0.21/0.63    sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.63    inference(forward_demodulation,[],[f190,f48])).
% 0.21/0.63  fof(f48,plain,(
% 0.21/0.63    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.63    inference(cnf_transformation,[],[f14])).
% 0.21/0.63  fof(f14,axiom,(
% 0.21/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.63  fof(f190,plain,(
% 0.21/0.63    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK0))),
% 0.21/0.63    inference(superposition,[],[f162,f146])).
% 0.21/0.63  fof(f146,plain,(
% 0.21/0.63    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.63    inference(resolution,[],[f90,f44])).
% 0.21/0.63  fof(f44,plain,(
% 0.21/0.63    r1_tarski(sK0,sK1)),
% 0.21/0.63    inference(cnf_transformation,[],[f40])).
% 0.21/0.63  fof(f40,plain,(
% 0.21/0.63    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f39])).
% 0.21/0.63  fof(f39,plain,(
% 0.21/0.63    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.63    introduced(choice_axiom,[])).
% 0.21/0.63  fof(f25,plain,(
% 0.21/0.63    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.63    inference(flattening,[],[f24])).
% 0.21/0.63  fof(f24,plain,(
% 0.21/0.63    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.63    inference(ennf_transformation,[],[f22])).
% 0.21/0.63  fof(f22,negated_conjecture,(
% 0.21/0.63    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.21/0.63    inference(negated_conjecture,[],[f21])).
% 0.21/0.63  fof(f21,conjecture,(
% 0.21/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.21/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 0.21/0.63  fof(f90,plain,(
% 0.21/0.63    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.63    inference(forward_demodulation,[],[f88,f47])).
% 0.21/0.63  fof(f47,plain,(
% 0.21/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.63    inference(cnf_transformation,[],[f14])).
% 0.21/0.63  fof(f88,plain,(
% 0.21/0.63    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.63    inference(resolution,[],[f57,f46])).
% 0.21/0.63  fof(f46,plain,(
% 0.21/0.63    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f23])).
% 0.21/0.63  fof(f23,plain,(
% 0.21/0.63    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.63    inference(pure_predicate_removal,[],[f16])).
% 0.21/0.63  fof(f16,axiom,(
% 0.21/0.63    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.63  fof(f57,plain,(
% 0.21/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.63    inference(cnf_transformation,[],[f32])).
% 0.21/0.63  fof(f32,plain,(
% 0.21/0.63    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.63    inference(flattening,[],[f31])).
% 0.21/0.63  fof(f31,plain,(
% 0.21/0.63    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.63    inference(ennf_transformation,[],[f15])).
% 0.21/0.63  fof(f15,axiom,(
% 0.21/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.63  fof(f162,plain,(
% 0.21/0.63    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) )),
% 0.21/0.63    inference(backward_demodulation,[],[f82,f161])).
% 0.21/0.63  fof(f161,plain,(
% 0.21/0.63    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k9_relat_1(k6_relat_1(X2),X1)) )),
% 0.21/0.63    inference(forward_demodulation,[],[f160,f48])).
% 0.21/0.63  fof(f160,plain,(
% 0.21/0.63    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X2),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X2,X1)))) )),
% 0.21/0.63    inference(forward_demodulation,[],[f159,f52])).
% 0.21/0.63  fof(f52,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f17])).
% 0.21/0.63  fof(f17,axiom,(
% 0.21/0.63    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.63  fof(f159,plain,(
% 0.21/0.63    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),X1)) )),
% 0.21/0.63    inference(forward_demodulation,[],[f155,f48])).
% 0.21/0.63  fof(f155,plain,(
% 0.21/0.63    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),k2_relat_1(k6_relat_1(X1)))) )),
% 0.21/0.63    inference(resolution,[],[f98,f46])).
% 0.21/0.63  fof(f98,plain,(
% 0.21/0.63    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),k2_relat_1(X1))) )),
% 0.21/0.63    inference(resolution,[],[f49,f46])).
% 0.21/0.63  fof(f49,plain,(
% 0.21/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f26])).
% 0.21/0.63  fof(f26,plain,(
% 0.21/0.63    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.63    inference(ennf_transformation,[],[f13])).
% 0.21/0.63  fof(f13,axiom,(
% 0.21/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.63  fof(f82,plain,(
% 0.21/0.63    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.63    inference(resolution,[],[f55,f46])).
% 0.21/0.63  fof(f55,plain,(
% 0.21/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f29])).
% 0.21/0.63  fof(f29,plain,(
% 0.21/0.63    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.63    inference(ennf_transformation,[],[f12])).
% 0.21/0.63  fof(f12,axiom,(
% 0.21/0.63    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.63  fof(f119,plain,(
% 0.21/0.63    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 0.21/0.63    inference(superposition,[],[f45,f106])).
% 0.21/0.63  fof(f106,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))) )),
% 0.21/0.63    inference(forward_demodulation,[],[f103,f100])).
% 0.21/0.63  fof(f100,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))) )),
% 0.21/0.63    inference(resolution,[],[f63,f43])).
% 0.21/0.63  fof(f43,plain,(
% 0.21/0.63    v1_relat_1(sK2)),
% 0.21/0.63    inference(cnf_transformation,[],[f40])).
% 0.21/0.63  fof(f63,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f35])).
% 0.21/0.63  fof(f35,plain,(
% 0.21/0.63    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.63    inference(ennf_transformation,[],[f19])).
% 0.21/0.63  fof(f19,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).
% 0.21/0.63  fof(f103,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)) )),
% 0.21/0.63    inference(resolution,[],[f64,f43])).
% 0.21/0.63  fof(f64,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f36])).
% 0.21/0.63  fof(f36,plain,(
% 0.21/0.63    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 0.21/0.63    inference(ennf_transformation,[],[f20])).
% 0.21/0.63  fof(f20,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 0.21/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).
% 0.21/0.63  fof(f45,plain,(
% 0.21/0.63    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 0.21/0.63    inference(cnf_transformation,[],[f40])).
% 0.21/0.63  % SZS output end Proof for theBenchmark
% 0.21/0.63  % (32221)------------------------------
% 0.21/0.63  % (32221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.63  % (32221)Termination reason: Refutation
% 0.21/0.63  
% 0.21/0.63  % (32221)Memory used [KB]: 1918
% 0.21/0.63  % (32221)Time elapsed: 0.171 s
% 0.21/0.63  % (32221)------------------------------
% 0.21/0.63  % (32221)------------------------------
% 0.21/0.63  % (32236)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.63  % (32213)Success in time 0.261 s
%------------------------------------------------------------------------------
