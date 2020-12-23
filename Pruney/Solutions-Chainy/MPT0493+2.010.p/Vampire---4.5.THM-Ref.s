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
% DateTime   : Thu Dec  3 12:48:21 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   55 (  75 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 175 expanded)
%              Number of equality atoms :   35 (  53 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f629,plain,(
    $false ),
    inference(subsumption_resolution,[],[f628,f28])).

fof(f28,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f628,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f592,f30])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f592,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f339,f246])).

fof(f246,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f242,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f242,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k1_xboole_0 = k4_xboole_0(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f221,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f40,f29])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

% (6786)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f221,plain,(
    ! [X1] :
      ( v1_xboole_0(k4_xboole_0(X1,k1_relat_1(sK1)))
      | ~ r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f62,f106])).

fof(f106,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),k1_relat_1(sK1))
      | ~ r1_tarski(X2,sK0) ) ),
    inference(resolution,[],[f100,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r1_tarski(X1,k1_relat_1(sK1))
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f98,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f98,plain,(
    ! [X2] :
      ( r1_tarski(X2,k1_relat_1(sK1))
      | ~ r1_tarski(X2,sK0) ) ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
      | v1_xboole_0(k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f339,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(superposition,[],[f135,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f135,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:40:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.57  % (6783)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.57  % (6775)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.57  % (6791)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.55/0.57  % (6782)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.55/0.58  % (6790)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.55/0.58  % (6768)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.58  % (6763)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.55/0.59  % (6765)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.59  % (6776)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.59  % (6774)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.55/0.59  % (6764)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.55/0.59  % (6767)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.59  % (6766)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.55/0.59  % (6784)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.84/0.59  % (6777)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.84/0.60  % (6770)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.84/0.60  % (6785)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.84/0.60  % (6781)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.84/0.61  % (6771)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.84/0.61  % (6780)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.84/0.61  % (6768)Refutation found. Thanks to Tanya!
% 1.84/0.61  % SZS status Theorem for theBenchmark
% 1.84/0.61  % SZS output start Proof for theBenchmark
% 1.84/0.61  fof(f629,plain,(
% 1.84/0.61    $false),
% 1.84/0.61    inference(subsumption_resolution,[],[f628,f28])).
% 1.84/0.61  fof(f28,plain,(
% 1.84/0.61    sK0 != k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.84/0.61    inference(cnf_transformation,[],[f23])).
% 1.84/0.61  fof(f23,plain,(
% 1.84/0.61    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.84/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).
% 1.84/0.61  fof(f22,plain,(
% 1.84/0.61    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.84/0.61    introduced(choice_axiom,[])).
% 1.84/0.61  fof(f15,plain,(
% 1.84/0.61    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.84/0.61    inference(flattening,[],[f14])).
% 1.84/0.61  fof(f14,plain,(
% 1.84/0.61    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f13])).
% 1.84/0.61  fof(f13,negated_conjecture,(
% 1.84/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.84/0.61    inference(negated_conjecture,[],[f12])).
% 1.84/0.61  fof(f12,conjecture,(
% 1.84/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.84/0.61  fof(f628,plain,(
% 1.84/0.61    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.84/0.61    inference(forward_demodulation,[],[f592,f30])).
% 1.84/0.61  fof(f30,plain,(
% 1.84/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f6])).
% 1.84/0.61  fof(f6,axiom,(
% 1.84/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.84/0.61  fof(f592,plain,(
% 1.84/0.61    k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.84/0.61    inference(superposition,[],[f339,f246])).
% 1.84/0.61  fof(f246,plain,(
% 1.84/0.61    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 1.84/0.61    inference(resolution,[],[f242,f44])).
% 1.84/0.61  fof(f44,plain,(
% 1.84/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.84/0.61    inference(equality_resolution,[],[f38])).
% 1.84/0.61  fof(f38,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.84/0.61    inference(cnf_transformation,[],[f25])).
% 1.84/0.61  fof(f25,plain,(
% 1.84/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.61    inference(flattening,[],[f24])).
% 1.84/0.61  fof(f24,plain,(
% 1.84/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.61    inference(nnf_transformation,[],[f3])).
% 1.84/0.61  fof(f3,axiom,(
% 1.84/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.84/0.61  fof(f242,plain,(
% 1.84/0.61    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_xboole_0 = k4_xboole_0(X0,k1_relat_1(sK1))) )),
% 1.84/0.61    inference(resolution,[],[f221,f50])).
% 1.84/0.61  fof(f50,plain,(
% 1.84/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.84/0.61    inference(resolution,[],[f40,f29])).
% 1.84/0.61  fof(f29,plain,(
% 1.84/0.61    v1_xboole_0(k1_xboole_0)),
% 1.84/0.61    inference(cnf_transformation,[],[f2])).
% 1.84/0.61  fof(f2,axiom,(
% 1.84/0.61    v1_xboole_0(k1_xboole_0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.84/0.61  % (6786)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.84/0.61  fof(f40,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f19])).
% 1.84/0.61  fof(f19,plain,(
% 1.84/0.61    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.84/0.61    inference(ennf_transformation,[],[f10])).
% 1.84/0.61  fof(f10,axiom,(
% 1.84/0.61    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.84/0.61  fof(f221,plain,(
% 1.84/0.61    ( ! [X1] : (v1_xboole_0(k4_xboole_0(X1,k1_relat_1(sK1))) | ~r1_tarski(X1,sK0)) )),
% 1.84/0.61    inference(resolution,[],[f62,f106])).
% 1.84/0.61  fof(f106,plain,(
% 1.84/0.61    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k1_relat_1(sK1)) | ~r1_tarski(X2,sK0)) )),
% 1.84/0.61    inference(resolution,[],[f100,f32])).
% 1.84/0.61  fof(f32,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f5])).
% 1.84/0.61  fof(f5,axiom,(
% 1.84/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.84/0.61  fof(f100,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(X1,k1_relat_1(sK1)) | ~r1_tarski(X0,sK0)) )),
% 1.84/0.61    inference(resolution,[],[f98,f41])).
% 1.84/0.61  fof(f41,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f21])).
% 1.84/0.61  fof(f21,plain,(
% 1.84/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.84/0.61    inference(flattening,[],[f20])).
% 1.84/0.61  fof(f20,plain,(
% 1.84/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.84/0.61    inference(ennf_transformation,[],[f4])).
% 1.84/0.61  fof(f4,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.84/0.61  fof(f98,plain,(
% 1.84/0.61    ( ! [X2] : (r1_tarski(X2,k1_relat_1(sK1)) | ~r1_tarski(X2,sK0)) )),
% 1.84/0.61    inference(resolution,[],[f41,f27])).
% 1.84/0.61  fof(f27,plain,(
% 1.84/0.61    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.84/0.61    inference(cnf_transformation,[],[f23])).
% 1.84/0.61  fof(f62,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1) | v1_xboole_0(k4_xboole_0(X0,X1))) )),
% 1.84/0.61    inference(resolution,[],[f35,f31])).
% 1.84/0.61  fof(f31,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f9])).
% 1.84/0.61  fof(f9,axiom,(
% 1.84/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.84/0.61  fof(f35,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f17])).
% 1.84/0.61  fof(f17,plain,(
% 1.84/0.61    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.84/0.61    inference(flattening,[],[f16])).
% 1.84/0.61  fof(f16,plain,(
% 1.84/0.61    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f8])).
% 1.84/0.61  fof(f8,axiom,(
% 1.84/0.61    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.84/0.61  fof(f339,plain,(
% 1.84/0.61    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.84/0.61    inference(superposition,[],[f135,f42])).
% 1.84/0.61  fof(f42,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.84/0.61    inference(definition_unfolding,[],[f33,f34,f34])).
% 1.84/0.61  fof(f34,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f7])).
% 1.84/0.61  fof(f7,axiom,(
% 1.84/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.84/0.61  fof(f33,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f1])).
% 1.84/0.61  fof(f1,axiom,(
% 1.84/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.84/0.61  fof(f135,plain,(
% 1.84/0.61    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))) )),
% 1.84/0.61    inference(resolution,[],[f43,f26])).
% 1.84/0.61  fof(f26,plain,(
% 1.84/0.61    v1_relat_1(sK1)),
% 1.84/0.61    inference(cnf_transformation,[],[f23])).
% 1.84/0.61  fof(f43,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 1.84/0.61    inference(definition_unfolding,[],[f36,f34])).
% 1.84/0.61  fof(f36,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f18])).
% 1.84/0.61  fof(f18,plain,(
% 1.84/0.61    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f11])).
% 1.84/0.61  fof(f11,axiom,(
% 1.84/0.61    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.84/0.61  % SZS output end Proof for theBenchmark
% 1.84/0.61  % (6768)------------------------------
% 1.84/0.61  % (6768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (6768)Termination reason: Refutation
% 1.84/0.61  
% 1.84/0.61  % (6768)Memory used [KB]: 11001
% 1.84/0.61  % (6768)Time elapsed: 0.171 s
% 1.84/0.61  % (6768)------------------------------
% 1.84/0.61  % (6768)------------------------------
% 1.84/0.61  % (6772)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.84/0.61  % (6779)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.84/0.61  % (6789)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.84/0.61  % (6769)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.84/0.61  % (6778)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.84/0.62  % (6787)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.84/0.62  % (6761)Success in time 0.255 s
%------------------------------------------------------------------------------
