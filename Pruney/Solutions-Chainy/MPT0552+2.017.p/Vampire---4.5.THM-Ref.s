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
% DateTime   : Thu Dec  3 12:49:47 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 130 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 303 expanded)
%              Number of equality atoms :   21 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1829,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1285,f27,f1483,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f1483,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0)) ),
    inference(superposition,[],[f1285,f70])).

fof(f70,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f44,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f32,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f27,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f1285,plain,(
    ! [X39,X38] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X38,X39)),k9_relat_1(sK2,X38)) ),
    inference(superposition,[],[f80,f298])).

fof(f298,plain,(
    ! [X17,X16] : k2_xboole_0(X16,k3_xboole_0(X16,X17)) = X16 ),
    inference(subsumption_resolution,[],[f293,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f293,plain,(
    ! [X17,X16] :
      ( k2_xboole_0(X16,k3_xboole_0(X16,X17)) = X16
      | ~ r1_tarski(X16,k2_xboole_0(X16,k3_xboole_0(X16,X17))) ) ),
    inference(resolution,[],[f93,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f93,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(forward_demodulation,[],[f90,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f90,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),X1),X1) ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f40,f42])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f64,f30])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f46,f61])).

fof(f61,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(resolution,[],[f37,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (28486)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (28488)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (28478)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (28503)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (28502)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (28481)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (28505)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (28487)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (28496)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (28496)Refutation not found, incomplete strategy% (28496)------------------------------
% 0.21/0.54  % (28496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28496)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28496)Memory used [KB]: 10618
% 0.21/0.54  % (28496)Time elapsed: 0.138 s
% 0.21/0.54  % (28496)------------------------------
% 0.21/0.54  % (28496)------------------------------
% 0.21/0.55  % (28482)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (28508)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (28499)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (28483)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (28479)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (28485)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (28493)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.57  % (28491)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.57  % (28494)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (28507)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (28495)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (28497)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.58  % (28500)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.58  % (28510)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.58  % (28506)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.59  % (28492)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.85/0.60  % (28501)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.85/0.61  % (28498)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.02/0.62  % (28490)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.02/0.62  % (28509)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.02/0.63  % (28509)Refutation not found, incomplete strategy% (28509)------------------------------
% 2.02/0.63  % (28509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.63  % (28509)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.63  
% 2.02/0.63  % (28509)Memory used [KB]: 10618
% 2.02/0.63  % (28509)Time elapsed: 0.155 s
% 2.02/0.63  % (28509)------------------------------
% 2.02/0.63  % (28509)------------------------------
% 2.11/0.63  % (28490)Refutation not found, incomplete strategy% (28490)------------------------------
% 2.11/0.63  % (28490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.63  % (28490)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.63  
% 2.11/0.63  % (28490)Memory used [KB]: 10618
% 2.11/0.63  % (28490)Time elapsed: 0.158 s
% 2.11/0.63  % (28490)------------------------------
% 2.11/0.63  % (28490)------------------------------
% 2.11/0.63  % (28480)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 2.11/0.65  % (28486)Refutation found. Thanks to Tanya!
% 2.11/0.65  % SZS status Theorem for theBenchmark
% 2.11/0.65  % SZS output start Proof for theBenchmark
% 2.11/0.65  fof(f1829,plain,(
% 2.11/0.65    $false),
% 2.11/0.65    inference(unit_resulting_resolution,[],[f1285,f27,f1483,f39])).
% 2.11/0.65  fof(f39,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f19])).
% 2.11/0.65  fof(f19,plain,(
% 2.11/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.11/0.65    inference(flattening,[],[f18])).
% 2.11/0.65  fof(f18,plain,(
% 2.11/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.11/0.65    inference(ennf_transformation,[],[f5])).
% 2.11/0.65  fof(f5,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.11/0.65  fof(f1483,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0))) )),
% 2.11/0.65    inference(superposition,[],[f1285,f70])).
% 2.11/0.65  fof(f70,plain,(
% 2.11/0.65    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 2.11/0.65    inference(superposition,[],[f44,f32])).
% 2.11/0.65  fof(f32,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f11])).
% 2.11/0.65  fof(f11,axiom,(
% 2.11/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.11/0.65  fof(f44,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 2.11/0.65    inference(superposition,[],[f32,f29])).
% 2.11/0.65  fof(f29,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f7])).
% 2.11/0.65  fof(f7,axiom,(
% 2.11/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.11/0.65  fof(f27,plain,(
% 2.11/0.65    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 2.11/0.65    inference(cnf_transformation,[],[f23])).
% 2.11/0.65  fof(f23,plain,(
% 2.11/0.65    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22])).
% 2.11/0.65  fof(f22,plain,(
% 2.11/0.65    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f15,plain,(
% 2.11/0.65    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 2.11/0.65    inference(ennf_transformation,[],[f14])).
% 2.11/0.65  fof(f14,negated_conjecture,(
% 2.11/0.65    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.11/0.65    inference(negated_conjecture,[],[f13])).
% 2.11/0.65  fof(f13,conjecture,(
% 2.11/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 2.11/0.65  fof(f1285,plain,(
% 2.11/0.65    ( ! [X39,X38] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X38,X39)),k9_relat_1(sK2,X38))) )),
% 2.11/0.65    inference(superposition,[],[f80,f298])).
% 2.11/0.65  fof(f298,plain,(
% 2.11/0.65    ( ! [X17,X16] : (k2_xboole_0(X16,k3_xboole_0(X16,X17)) = X16) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f293,f46])).
% 2.11/0.65  fof(f46,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.11/0.65    inference(resolution,[],[f38,f42])).
% 2.11/0.65  fof(f42,plain,(
% 2.11/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.11/0.65    inference(equality_resolution,[],[f34])).
% 2.11/0.65  fof(f34,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.11/0.65    inference(cnf_transformation,[],[f25])).
% 2.11/0.65  fof(f25,plain,(
% 2.11/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.65    inference(flattening,[],[f24])).
% 2.11/0.65  fof(f24,plain,(
% 2.11/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.65    inference(nnf_transformation,[],[f2])).
% 2.11/0.65  fof(f2,axiom,(
% 2.11/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.11/0.65  fof(f38,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f17])).
% 2.11/0.65  fof(f17,plain,(
% 2.11/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.11/0.65    inference(ennf_transformation,[],[f3])).
% 2.11/0.65  fof(f3,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.11/0.65  fof(f293,plain,(
% 2.11/0.65    ( ! [X17,X16] : (k2_xboole_0(X16,k3_xboole_0(X16,X17)) = X16 | ~r1_tarski(X16,k2_xboole_0(X16,k3_xboole_0(X16,X17)))) )),
% 2.11/0.65    inference(resolution,[],[f93,f35])).
% 2.11/0.65  fof(f35,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f25])).
% 2.11/0.65  fof(f93,plain,(
% 2.11/0.65    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(X1,k3_xboole_0(X1,X2)),X1)) )),
% 2.11/0.65    inference(forward_demodulation,[],[f90,f30])).
% 2.11/0.65  fof(f30,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f1])).
% 2.11/0.65  fof(f1,axiom,(
% 2.11/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.11/0.65  fof(f90,plain,(
% 2.11/0.65    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),X1),X1)) )),
% 2.11/0.65    inference(resolution,[],[f58,f28])).
% 2.11/0.65  fof(f28,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f4])).
% 2.11/0.65  fof(f4,axiom,(
% 2.11/0.65    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.11/0.65  fof(f58,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X1),X1)) )),
% 2.11/0.65    inference(resolution,[],[f40,f42])).
% 2.11/0.65  fof(f40,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f21])).
% 2.11/0.65  fof(f21,plain,(
% 2.11/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.11/0.65    inference(flattening,[],[f20])).
% 2.11/0.65  fof(f20,plain,(
% 2.11/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.11/0.65    inference(ennf_transformation,[],[f6])).
% 2.11/0.65  fof(f6,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.11/0.65  fof(f80,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X1,X0)))) )),
% 2.11/0.65    inference(superposition,[],[f64,f30])).
% 2.11/0.65  fof(f64,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X0,X1)))) )),
% 2.11/0.65    inference(superposition,[],[f46,f61])).
% 2.11/0.65  fof(f61,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 2.11/0.65    inference(resolution,[],[f37,f26])).
% 2.11/0.65  fof(f26,plain,(
% 2.11/0.65    v1_relat_1(sK2)),
% 2.11/0.65    inference(cnf_transformation,[],[f23])).
% 2.11/0.65  fof(f37,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f16])).
% 2.11/0.65  fof(f16,plain,(
% 2.11/0.65    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.11/0.65    inference(ennf_transformation,[],[f12])).
% 2.11/0.65  fof(f12,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 2.11/0.65  % SZS output end Proof for theBenchmark
% 2.11/0.65  % (28486)------------------------------
% 2.11/0.65  % (28486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.65  % (28486)Termination reason: Refutation
% 2.11/0.65  
% 2.11/0.65  % (28486)Memory used [KB]: 3454
% 2.11/0.65  % (28486)Time elapsed: 0.196 s
% 2.11/0.65  % (28486)------------------------------
% 2.11/0.65  % (28486)------------------------------
% 2.11/0.66  % (28472)Success in time 0.294 s
%------------------------------------------------------------------------------
