%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:37 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   41 (  63 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 135 expanded)
%              Number of equality atoms :   30 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(subsumption_resolution,[],[f74,f31])).

fof(f31,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f21,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f74,plain,(
    k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(superposition,[],[f61,f62])).

fof(f62,plain,(
    ! [X0] : k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X0)) = k4_xboole_0(sK2,k7_relat_1(sK2,X0)) ),
    inference(superposition,[],[f36,f45])).

fof(f45,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f37,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f37,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(sK2),X4)
      | sK2 = k7_relat_1(sK2,X4) ) ),
    inference(resolution,[],[f19,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X2,X3] : k7_relat_1(sK2,k4_xboole_0(X2,X3)) = k4_xboole_0(k7_relat_1(sK2,X2),k7_relat_1(sK2,X3)) ),
    inference(resolution,[],[f19,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(definition_unfolding,[],[f28,f22,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(f61,plain,(
    ! [X5] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k4_xboole_0(X5,sK1)),sK0) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1)) ),
    inference(resolution,[],[f20,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) ) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) ) ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:06:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (9428)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (9427)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.56  % (9428)Refutation not found, incomplete strategy% (9428)------------------------------
% 0.21/0.56  % (9428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9428)Memory used [KB]: 1663
% 0.21/0.56  % (9428)Time elapsed: 0.115 s
% 0.21/0.56  % (9428)------------------------------
% 0.21/0.56  % (9428)------------------------------
% 0.21/0.56  % (9453)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (9431)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.51/0.57  % (9437)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.51/0.57  % (9430)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.51/0.57  % (9453)Refutation not found, incomplete strategy% (9453)------------------------------
% 1.51/0.57  % (9453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (9453)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (9453)Memory used [KB]: 6268
% 1.51/0.57  % (9453)Time elapsed: 0.140 s
% 1.51/0.57  % (9453)------------------------------
% 1.51/0.57  % (9453)------------------------------
% 1.51/0.57  % (9445)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.51/0.57  % (9436)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.51/0.57  % (9452)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.51/0.57  % (9432)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.51/0.57  % (9437)Refutation not found, incomplete strategy% (9437)------------------------------
% 1.51/0.57  % (9437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (9437)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (9437)Memory used [KB]: 10746
% 1.51/0.57  % (9437)Time elapsed: 0.141 s
% 1.51/0.57  % (9437)------------------------------
% 1.51/0.57  % (9437)------------------------------
% 1.73/0.59  % (9433)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.73/0.59  % (9434)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.73/0.60  % (9429)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.73/0.60  % (9435)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.73/0.60  % (9455)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.73/0.60  % (9446)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.73/0.60  % (9449)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.73/0.60  % (9450)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.73/0.60  % (9444)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.73/0.61  % (9443)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.73/0.61  % (9444)Refutation found. Thanks to Tanya!
% 1.73/0.61  % SZS status Theorem for theBenchmark
% 1.73/0.61  % SZS output start Proof for theBenchmark
% 1.73/0.61  fof(f81,plain,(
% 1.73/0.61    $false),
% 1.73/0.61    inference(subsumption_resolution,[],[f74,f31])).
% 1.73/0.61  fof(f31,plain,(
% 1.73/0.61    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.73/0.61    inference(definition_unfolding,[],[f21,f22])).
% 1.73/0.61  fof(f22,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f4])).
% 1.73/0.61  fof(f4,axiom,(
% 1.73/0.61    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.73/0.61  fof(f21,plain,(
% 1.73/0.61    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.73/0.61    inference(cnf_transformation,[],[f11])).
% 1.73/0.61  fof(f11,plain,(
% 1.73/0.61    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.73/0.61    inference(flattening,[],[f10])).
% 1.73/0.61  fof(f10,plain,(
% 1.73/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.73/0.61    inference(ennf_transformation,[],[f9])).
% 1.73/0.61  fof(f9,negated_conjecture,(
% 1.73/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.73/0.61    inference(negated_conjecture,[],[f8])).
% 1.73/0.61  fof(f8,conjecture,(
% 1.73/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 1.73/0.61  fof(f74,plain,(
% 1.73/0.61    k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.73/0.61    inference(superposition,[],[f61,f62])).
% 1.73/0.61  fof(f62,plain,(
% 1.73/0.61    ( ! [X0] : (k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X0)) = k4_xboole_0(sK2,k7_relat_1(sK2,X0))) )),
% 1.73/0.61    inference(superposition,[],[f36,f45])).
% 1.73/0.61  fof(f45,plain,(
% 1.73/0.61    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 1.73/0.61    inference(resolution,[],[f37,f34])).
% 1.73/0.61  fof(f34,plain,(
% 1.73/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.73/0.61    inference(equality_resolution,[],[f25])).
% 1.73/0.61  fof(f25,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.73/0.61    inference(cnf_transformation,[],[f2])).
% 1.73/0.61  fof(f2,axiom,(
% 1.73/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.73/0.61  fof(f37,plain,(
% 1.73/0.61    ( ! [X4] : (~r1_tarski(k1_relat_1(sK2),X4) | sK2 = k7_relat_1(sK2,X4)) )),
% 1.73/0.61    inference(resolution,[],[f19,f23])).
% 1.73/0.61  fof(f23,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.73/0.61    inference(cnf_transformation,[],[f13])).
% 1.73/0.61  fof(f13,plain,(
% 1.73/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.73/0.61    inference(flattening,[],[f12])).
% 1.73/0.61  fof(f12,plain,(
% 1.73/0.61    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f7])).
% 1.73/0.61  fof(f7,axiom,(
% 1.73/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.73/0.61  fof(f19,plain,(
% 1.73/0.61    v1_relat_1(sK2)),
% 1.73/0.61    inference(cnf_transformation,[],[f11])).
% 1.73/0.61  fof(f36,plain,(
% 1.73/0.61    ( ! [X2,X3] : (k7_relat_1(sK2,k4_xboole_0(X2,X3)) = k4_xboole_0(k7_relat_1(sK2,X2),k7_relat_1(sK2,X3))) )),
% 1.73/0.61    inference(resolution,[],[f19,f32])).
% 1.73/0.61  fof(f32,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 1.73/0.61    inference(definition_unfolding,[],[f28,f22,f22])).
% 1.73/0.61  fof(f28,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f15])).
% 1.73/0.61  fof(f15,plain,(
% 1.73/0.61    ! [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.73/0.61    inference(ennf_transformation,[],[f5])).
% 1.73/0.61  fof(f5,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).
% 1.73/0.61  fof(f61,plain,(
% 1.73/0.61    ( ! [X5] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k4_xboole_0(X5,sK1)),sK0)) )),
% 1.73/0.61    inference(resolution,[],[f50,f38])).
% 1.73/0.61  fof(f38,plain,(
% 1.73/0.61    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,sK1))) )),
% 1.73/0.61    inference(resolution,[],[f20,f30])).
% 1.73/0.61  fof(f30,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f18])).
% 1.73/0.61  fof(f18,plain,(
% 1.73/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f3])).
% 1.73/0.61  fof(f3,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.73/0.61  fof(f20,plain,(
% 1.73/0.61    r1_tarski(sK0,sK1)),
% 1.73/0.61    inference(cnf_transformation,[],[f11])).
% 1.73/0.61  fof(f50,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)) )),
% 1.73/0.61    inference(resolution,[],[f35,f24])).
% 1.73/0.61  fof(f24,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f14])).
% 1.73/0.61  fof(f14,plain,(
% 1.73/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f1])).
% 1.73/0.61  fof(f1,axiom,(
% 1.73/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.73/0.61  fof(f35,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)) )),
% 1.73/0.61    inference(resolution,[],[f19,f29])).
% 1.73/0.61  fof(f29,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f17])).
% 1.73/0.61  fof(f17,plain,(
% 1.73/0.61    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.73/0.61    inference(flattening,[],[f16])).
% 1.73/0.61  fof(f16,plain,(
% 1.73/0.61    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.73/0.61    inference(ennf_transformation,[],[f6])).
% 1.73/0.61  fof(f6,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 1.73/0.61  % SZS output end Proof for theBenchmark
% 1.73/0.61  % (9443)Refutation not found, incomplete strategy% (9443)------------------------------
% 1.73/0.61  % (9443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (9443)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.61  % (9444)------------------------------
% 1.73/0.61  % (9444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  
% 1.73/0.61  % (9444)Termination reason: Refutation
% 1.73/0.61  
% 1.73/0.61  % (9443)Memory used [KB]: 10618
% 1.73/0.61  % (9443)Time elapsed: 0.167 s
% 1.73/0.61  % (9444)Memory used [KB]: 1791
% 1.73/0.61  % (9443)------------------------------
% 1.73/0.61  % (9443)------------------------------
% 1.73/0.61  % (9444)Time elapsed: 0.168 s
% 1.73/0.61  % (9444)------------------------------
% 1.73/0.61  % (9444)------------------------------
% 1.73/0.61  % (9426)Success in time 0.243 s
%------------------------------------------------------------------------------
