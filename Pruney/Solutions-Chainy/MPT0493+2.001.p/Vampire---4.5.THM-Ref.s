%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:20 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  78 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  104 ( 155 expanded)
%              Number of equality atoms :   39 (  62 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f447,plain,(
    $false ),
    inference(subsumption_resolution,[],[f444,f29])).

fof(f29,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f444,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f163,f156])).

fof(f156,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f51,f46])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f27,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f163,plain,(
    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f161,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f161,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f47,f122])).

fof(f122,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f91,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f91,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f89,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f89,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(superposition,[],[f61,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f61,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,k1_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f56,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f28,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f28,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (5900)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.55  % (5916)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.56/0.57  % (5908)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.57  % (5896)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.57  % (5917)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.56/0.57  % (5907)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.56/0.58  % (5906)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.56/0.58  % (5909)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.58  % (5895)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.56/0.59  % (5894)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.56/0.59  % (5912)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.56/0.59  % (5898)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.56/0.59  % (5897)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.56/0.59  % (5904)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.56/0.59  % (5899)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.56/0.59  % (5901)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.60  % (5910)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.60  % (5921)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.56/0.61  % (5911)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.56/0.61  % (5915)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.56/0.61  % (5922)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.56/0.61  % (5919)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.56/0.61  % (5913)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.61  % (5923)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.56/0.61  % (5918)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.62  % (5905)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.56/0.62  % (5903)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.56/0.62  % (5902)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.56/0.62  % (5920)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.56/0.62  % (5920)Refutation not found, incomplete strategy% (5920)------------------------------
% 1.56/0.62  % (5920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (5920)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.62  
% 1.56/0.62  % (5920)Memory used [KB]: 6140
% 1.56/0.62  % (5920)Time elapsed: 0.200 s
% 1.56/0.62  % (5920)------------------------------
% 1.56/0.62  % (5920)------------------------------
% 1.56/0.63  % (5914)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.21/0.64  % (5905)Refutation found. Thanks to Tanya!
% 2.21/0.64  % SZS status Theorem for theBenchmark
% 2.21/0.64  % SZS output start Proof for theBenchmark
% 2.21/0.64  fof(f447,plain,(
% 2.21/0.64    $false),
% 2.21/0.64    inference(subsumption_resolution,[],[f444,f29])).
% 2.21/0.64  fof(f29,plain,(
% 2.21/0.64    sK0 != k1_relat_1(k7_relat_1(sK1,sK0))),
% 2.21/0.64    inference(cnf_transformation,[],[f24])).
% 2.21/0.64  fof(f24,plain,(
% 2.21/0.64    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 2.21/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).
% 2.21/0.64  fof(f23,plain,(
% 2.21/0.64    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 2.21/0.64    introduced(choice_axiom,[])).
% 2.21/0.64  fof(f17,plain,(
% 2.21/0.64    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.21/0.64    inference(flattening,[],[f16])).
% 2.21/0.64  fof(f16,plain,(
% 2.21/0.64    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.21/0.64    inference(ennf_transformation,[],[f15])).
% 2.21/0.64  fof(f15,negated_conjecture,(
% 2.21/0.64    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.21/0.64    inference(negated_conjecture,[],[f14])).
% 2.21/0.64  fof(f14,conjecture,(
% 2.21/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 2.21/0.64  fof(f444,plain,(
% 2.21/0.64    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 2.21/0.64    inference(superposition,[],[f163,f156])).
% 2.21/0.64  fof(f156,plain,(
% 2.21/0.64    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1)))) )),
% 2.21/0.64    inference(superposition,[],[f51,f46])).
% 2.21/0.64  fof(f46,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.21/0.64    inference(definition_unfolding,[],[f33,f36,f36])).
% 2.21/0.64  fof(f36,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f11])).
% 2.21/0.64  fof(f11,axiom,(
% 2.21/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.21/0.64  fof(f33,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f10])).
% 2.21/0.64  fof(f10,axiom,(
% 2.21/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.21/0.64  fof(f51,plain,(
% 2.21/0.64    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) )),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f27,f48])).
% 2.21/0.64  fof(f48,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 2.21/0.64    inference(definition_unfolding,[],[f38,f45])).
% 2.21/0.64  fof(f45,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.21/0.64    inference(definition_unfolding,[],[f35,f36])).
% 2.21/0.64  fof(f35,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f12])).
% 2.21/0.64  fof(f12,axiom,(
% 2.21/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.21/0.64  fof(f38,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f18])).
% 2.21/0.64  fof(f18,plain,(
% 2.21/0.64    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.21/0.64    inference(ennf_transformation,[],[f13])).
% 2.21/0.64  fof(f13,axiom,(
% 2.21/0.64    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 2.21/0.64  fof(f27,plain,(
% 2.21/0.64    v1_relat_1(sK1)),
% 2.21/0.64    inference(cnf_transformation,[],[f24])).
% 2.21/0.64  fof(f163,plain,(
% 2.21/0.64    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))),
% 2.21/0.64    inference(forward_demodulation,[],[f161,f31])).
% 2.21/0.64  fof(f31,plain,(
% 2.21/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.64    inference(cnf_transformation,[],[f6])).
% 2.21/0.64  fof(f6,axiom,(
% 2.21/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.21/0.64  fof(f161,plain,(
% 2.21/0.64    k4_xboole_0(sK0,k1_xboole_0) = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))),
% 2.21/0.64    inference(superposition,[],[f47,f122])).
% 2.21/0.64  fof(f122,plain,(
% 2.21/0.64    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f30,f91,f41])).
% 2.21/0.64  fof(f41,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f26])).
% 2.21/0.64  fof(f26,plain,(
% 2.21/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.64    inference(flattening,[],[f25])).
% 2.21/0.64  fof(f25,plain,(
% 2.21/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.64    inference(nnf_transformation,[],[f2])).
% 2.21/0.64  fof(f2,axiom,(
% 2.21/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.21/0.64  fof(f91,plain,(
% 2.21/0.64    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),X0)) )),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f89,f42])).
% 2.21/0.64  fof(f42,plain,(
% 2.21/0.64    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f19])).
% 2.21/0.64  fof(f19,plain,(
% 2.21/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.21/0.64    inference(ennf_transformation,[],[f7])).
% 2.21/0.64  fof(f7,axiom,(
% 2.21/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.21/0.64  fof(f89,plain,(
% 2.21/0.64    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(k1_relat_1(sK1),X0))) )),
% 2.21/0.64    inference(superposition,[],[f61,f34])).
% 2.21/0.64  fof(f34,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f1])).
% 2.21/0.64  fof(f1,axiom,(
% 2.21/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.21/0.64  fof(f61,plain,(
% 2.21/0.64    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,k1_relat_1(sK1)))) )),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f56,f43])).
% 2.21/0.64  fof(f43,plain,(
% 2.21/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f20])).
% 2.21/0.64  fof(f20,plain,(
% 2.21/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.21/0.64    inference(ennf_transformation,[],[f8])).
% 2.21/0.64  fof(f8,axiom,(
% 2.21/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.21/0.64  fof(f56,plain,(
% 2.21/0.64    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k1_relat_1(sK1))) )),
% 2.21/0.64    inference(unit_resulting_resolution,[],[f32,f28,f44])).
% 2.21/0.65  fof(f44,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f22,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.21/0.65    inference(flattening,[],[f21])).
% 2.21/0.65  fof(f21,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.21/0.65    inference(ennf_transformation,[],[f3])).
% 2.21/0.65  fof(f3,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.21/0.65  fof(f28,plain,(
% 2.21/0.65    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.21/0.65    inference(cnf_transformation,[],[f24])).
% 2.21/0.65  fof(f32,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f5])).
% 2.21/0.65  fof(f5,axiom,(
% 2.21/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.21/0.65  fof(f30,plain,(
% 2.21/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f4])).
% 2.21/0.65  fof(f4,axiom,(
% 2.21/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.21/0.65  fof(f47,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.21/0.65    inference(definition_unfolding,[],[f37,f45])).
% 2.21/0.65  fof(f37,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f9])).
% 2.21/0.65  fof(f9,axiom,(
% 2.21/0.65    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.21/0.65  % SZS output end Proof for theBenchmark
% 2.21/0.65  % (5905)------------------------------
% 2.21/0.65  % (5905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (5905)Termination reason: Refutation
% 2.21/0.65  
% 2.21/0.65  % (5905)Memory used [KB]: 6396
% 2.21/0.65  % (5905)Time elapsed: 0.225 s
% 2.21/0.65  % (5905)------------------------------
% 2.21/0.65  % (5905)------------------------------
% 2.21/0.67  % (5893)Success in time 0.305 s
%------------------------------------------------------------------------------
