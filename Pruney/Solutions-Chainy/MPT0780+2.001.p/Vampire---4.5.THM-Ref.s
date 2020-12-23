%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:56 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   53 (  81 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 157 expanded)
%              Number of equality atoms :   49 (  73 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(backward_demodulation,[],[f203,f280])).

fof(f280,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f276,f55])).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f276,plain,(
    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f246,f204])).

fof(f204,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(resolution,[],[f111,f51])).

fof(f51,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f109,f54])).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f68,f53])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f246,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(backward_demodulation,[],[f103,f240])).

fof(f240,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X2),X1) = k3_xboole_0(X2,X1) ),
    inference(forward_demodulation,[],[f239,f55])).

fof(f239,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X2),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f238,f63])).

fof(f63,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f238,plain,(
    ! [X2,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(forward_demodulation,[],[f234,f55])).

fof(f234,plain,(
    ! [X2,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),k2_relat_1(k6_relat_1(X1))) ),
    inference(resolution,[],[f130,f53])).

fof(f130,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),k2_relat_1(X1)) ) ),
    inference(resolution,[],[f56,f53])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f103,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f66,f53])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f203,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f172,f201])).

fof(f201,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f95,f62])).

fof(f62,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f62,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f172,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f52,f132])).

fof(f132,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f76,f50])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(f52,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:50:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (31510)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (31526)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (31518)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (31508)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (31505)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (31527)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (31505)Refutation not found, incomplete strategy% (31505)------------------------------
% 0.22/0.54  % (31505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31505)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31505)Memory used [KB]: 1663
% 0.22/0.54  % (31505)Time elapsed: 0.124 s
% 0.22/0.54  % (31505)------------------------------
% 0.22/0.54  % (31505)------------------------------
% 0.22/0.54  % (31506)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (31507)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (31511)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (31532)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (31530)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (31522)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (31509)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (31513)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (31516)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (31525)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (31524)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (31520)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (31517)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (31504)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (31514)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (31512)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.56  % (31511)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.56  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f282,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(trivial_inequality_removal,[],[f281])).
% 1.43/0.56  fof(f281,plain,(
% 1.43/0.56    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)),
% 1.43/0.56    inference(backward_demodulation,[],[f203,f280])).
% 1.43/0.56  fof(f280,plain,(
% 1.43/0.56    sK0 = k3_xboole_0(sK0,sK1)),
% 1.43/0.56    inference(forward_demodulation,[],[f276,f55])).
% 1.43/0.56  fof(f55,plain,(
% 1.43/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f18])).
% 1.43/0.56  fof(f18,axiom,(
% 1.43/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.43/0.56  fof(f276,plain,(
% 1.43/0.56    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK0))),
% 1.43/0.56    inference(superposition,[],[f246,f204])).
% 1.43/0.56  fof(f204,plain,(
% 1.43/0.56    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.43/0.56    inference(resolution,[],[f111,f51])).
% 1.43/0.56  fof(f51,plain,(
% 1.43/0.56    r1_tarski(sK0,sK1)),
% 1.43/0.56    inference(cnf_transformation,[],[f46])).
% 1.43/0.56  fof(f46,plain,(
% 1.43/0.56    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f45])).
% 1.43/0.56  fof(f45,plain,(
% 1.43/0.56    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f29,plain,(
% 1.43/0.56    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.43/0.56    inference(flattening,[],[f28])).
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.43/0.56    inference(ennf_transformation,[],[f26])).
% 1.43/0.56  fof(f26,negated_conjecture,(
% 1.43/0.56    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.43/0.56    inference(negated_conjecture,[],[f25])).
% 1.43/0.56  fof(f25,conjecture,(
% 1.43/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 1.43/0.56  fof(f111,plain,(
% 1.43/0.56    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f109,f54])).
% 1.43/0.56  fof(f54,plain,(
% 1.43/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f18])).
% 1.43/0.56  fof(f109,plain,(
% 1.43/0.56    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.43/0.56    inference(resolution,[],[f68,f53])).
% 1.43/0.56  fof(f53,plain,(
% 1.43/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f27])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.43/0.56    inference(pure_predicate_removal,[],[f21])).
% 1.43/0.56  fof(f21,axiom,(
% 1.43/0.56    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.43/0.56  fof(f68,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.43/0.56    inference(cnf_transformation,[],[f39])).
% 1.43/0.56  fof(f39,plain,(
% 1.43/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f38])).
% 1.43/0.56  fof(f38,plain,(
% 1.43/0.56    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f20])).
% 1.43/0.56  fof(f20,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.43/0.56  fof(f246,plain,(
% 1.43/0.56    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) )),
% 1.43/0.56    inference(backward_demodulation,[],[f103,f240])).
% 1.43/0.56  fof(f240,plain,(
% 1.43/0.56    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X2),X1) = k3_xboole_0(X2,X1)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f239,f55])).
% 1.43/0.56  fof(f239,plain,(
% 1.43/0.56    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X2),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X2,X1)))) )),
% 1.43/0.56    inference(forward_demodulation,[],[f238,f63])).
% 1.43/0.56  fof(f63,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f22])).
% 1.43/0.56  fof(f22,axiom,(
% 1.43/0.56    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.43/0.56  fof(f238,plain,(
% 1.43/0.56    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),X1)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f234,f55])).
% 1.43/0.56  fof(f234,plain,(
% 1.43/0.56    ( ! [X2,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),k2_relat_1(k6_relat_1(X1)))) )),
% 1.43/0.56    inference(resolution,[],[f130,f53])).
% 1.43/0.56  fof(f130,plain,(
% 1.43/0.56    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X2),k2_relat_1(X1))) )),
% 1.43/0.56    inference(resolution,[],[f56,f53])).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f30])).
% 1.43/0.56  fof(f30,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f16])).
% 1.43/0.56  fof(f16,axiom,(
% 1.43/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.43/0.56  fof(f103,plain,(
% 1.43/0.56    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 1.43/0.56    inference(resolution,[],[f66,f53])).
% 1.43/0.56  fof(f66,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f36])).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f15])).
% 1.43/0.56  fof(f15,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.43/0.56  fof(f203,plain,(
% 1.43/0.56    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 1.43/0.56    inference(backward_demodulation,[],[f172,f201])).
% 1.43/0.56  fof(f201,plain,(
% 1.43/0.56    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.43/0.56    inference(superposition,[],[f95,f62])).
% 1.43/0.56  fof(f62,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f10])).
% 1.43/0.56  fof(f10,axiom,(
% 1.43/0.56    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.43/0.56  fof(f95,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.43/0.56    inference(superposition,[],[f62,f60])).
% 1.43/0.56  fof(f60,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f3])).
% 1.43/0.56  fof(f3,axiom,(
% 1.43/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.43/0.56  fof(f172,plain,(
% 1.43/0.56    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK1,sK0))),
% 1.43/0.56    inference(superposition,[],[f52,f132])).
% 1.43/0.56  fof(f132,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))) )),
% 1.43/0.56    inference(resolution,[],[f76,f50])).
% 1.43/0.56  fof(f50,plain,(
% 1.43/0.56    v1_relat_1(sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f46])).
% 1.43/0.56  fof(f76,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f42])).
% 1.43/0.56  fof(f42,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.43/0.56    inference(ennf_transformation,[],[f24])).
% 1.43/0.56  fof(f24,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).
% 1.43/0.56  fof(f52,plain,(
% 1.43/0.56    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f46])).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (31511)------------------------------
% 1.43/0.56  % (31511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (31511)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (31511)Memory used [KB]: 1918
% 1.43/0.56  % (31511)Time elapsed: 0.079 s
% 1.43/0.56  % (31511)------------------------------
% 1.43/0.56  % (31511)------------------------------
% 1.43/0.56  % (31515)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.56  % (31533)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.56  % (31503)Success in time 0.195 s
%------------------------------------------------------------------------------
