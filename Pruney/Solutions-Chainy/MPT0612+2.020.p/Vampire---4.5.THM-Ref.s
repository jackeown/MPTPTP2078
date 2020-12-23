%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:38 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   45 (  88 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 223 expanded)
%              Number of equality atoms :   39 (  83 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f59,f23,f66])).

% (29905)Refutation not found, incomplete strategy% (29905)------------------------------
% (29905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29889)Termination reason: Refutation not found, incomplete strategy

% (29889)Memory used [KB]: 10746
% (29889)Time elapsed: 0.124 s
% (29889)------------------------------
% (29889)------------------------------
% (29905)Termination reason: Refutation not found, incomplete strategy

% (29905)Memory used [KB]: 6268
% (29905)Time elapsed: 0.122 s
% (29905)------------------------------
% (29905)------------------------------
% (29902)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (29880)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (29888)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f66,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X3)),X4)
      | ~ r1_xboole_0(k6_subset_1(k1_relat_1(sK2),X3),X4) ) ),
    inference(subsumption_resolution,[],[f64,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f64,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X3)),X4)
      | ~ r1_xboole_0(k6_subset_1(k1_relat_1(sK2),X3),X4)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f30,f48])).

fof(f48,plain,(
    ! [X0] : k6_subset_1(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),X0)) ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | k6_subset_1(sK2,k7_relat_1(sK2,X1)) = k7_relat_1(sK2,k6_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f31,f21])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f23,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] : r1_xboole_0(k6_subset_1(X0,sK1),sK0) ),
    inference(superposition,[],[f57,f42])).

fof(f42,plain,(
    ! [X0] : sK0 = k6_subset_1(sK0,k6_subset_1(X0,sK1)) ),
    inference(resolution,[],[f38,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_subset_1(X0,k6_subset_1(X2,X1)) = X0 ) ),
    inference(resolution,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k6_subset_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f57,plain,(
    ! [X4,X3] : r1_xboole_0(X3,k6_subset_1(X4,X3)) ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,(
    ! [X4,X3] :
      ( X3 != X3
      | r1_xboole_0(X3,k6_subset_1(X4,X3)) ) ),
    inference(superposition,[],[f33,f43])).

fof(f43,plain,(
    ! [X2,X1] : k6_subset_1(X1,k6_subset_1(X2,X1)) = X1 ),
    inference(resolution,[],[f38,f36])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:55:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (29879)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (29882)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.52  % (29893)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.52  % (29889)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.27/0.53  % (29893)Refutation not found, incomplete strategy% (29893)------------------------------
% 1.27/0.53  % (29893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (29893)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (29893)Memory used [KB]: 1663
% 1.27/0.53  % (29893)Time elapsed: 0.123 s
% 1.27/0.53  % (29893)------------------------------
% 1.27/0.53  % (29893)------------------------------
% 1.27/0.53  % (29901)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.53  % (29889)Refutation not found, incomplete strategy% (29889)------------------------------
% 1.27/0.53  % (29889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (29905)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.53  % (29901)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.53  % SZS output start Proof for theBenchmark
% 1.27/0.53  fof(f107,plain,(
% 1.27/0.53    $false),
% 1.27/0.53    inference(unit_resulting_resolution,[],[f59,f23,f66])).
% 1.27/0.54  % (29905)Refutation not found, incomplete strategy% (29905)------------------------------
% 1.27/0.54  % (29905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (29889)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (29889)Memory used [KB]: 10746
% 1.27/0.54  % (29889)Time elapsed: 0.124 s
% 1.27/0.54  % (29889)------------------------------
% 1.27/0.54  % (29889)------------------------------
% 1.27/0.54  % (29905)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (29905)Memory used [KB]: 6268
% 1.27/0.54  % (29905)Time elapsed: 0.122 s
% 1.27/0.54  % (29905)------------------------------
% 1.27/0.54  % (29905)------------------------------
% 1.27/0.54  % (29902)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.54  % (29880)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.45/0.54  % (29888)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.45/0.54  fof(f66,plain,(
% 1.45/0.54    ( ! [X4,X3] : (k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X3)),X4) | ~r1_xboole_0(k6_subset_1(k1_relat_1(sK2),X3),X4)) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f64,f21])).
% 1.45/0.54  fof(f21,plain,(
% 1.45/0.54    v1_relat_1(sK2)),
% 1.45/0.54    inference(cnf_transformation,[],[f17])).
% 1.45/0.54  fof(f17,plain,(
% 1.45/0.54    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).
% 1.45/0.54  fof(f16,plain,(
% 1.45/0.54    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f10,plain,(
% 1.45/0.54    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.45/0.54    inference(flattening,[],[f9])).
% 1.45/0.54  fof(f9,plain,(
% 1.45/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.45/0.54    inference(ennf_transformation,[],[f8])).
% 1.45/0.54  fof(f8,negated_conjecture,(
% 1.45/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.45/0.54    inference(negated_conjecture,[],[f7])).
% 1.45/0.54  fof(f7,conjecture,(
% 1.45/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 1.45/0.54  fof(f64,plain,(
% 1.45/0.54    ( ! [X4,X3] : (k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X3)),X4) | ~r1_xboole_0(k6_subset_1(k1_relat_1(sK2),X3),X4) | ~v1_relat_1(sK2)) )),
% 1.45/0.54    inference(superposition,[],[f30,f48])).
% 1.45/0.54  fof(f48,plain,(
% 1.45/0.54    ( ! [X0] : (k6_subset_1(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),X0))) )),
% 1.45/0.54    inference(resolution,[],[f44,f36])).
% 1.45/0.54  fof(f36,plain,(
% 1.45/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.45/0.54    inference(equality_resolution,[],[f26])).
% 1.45/0.54  fof(f26,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.45/0.54    inference(cnf_transformation,[],[f19])).
% 1.45/0.54  fof(f19,plain,(
% 1.45/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.54    inference(flattening,[],[f18])).
% 1.45/0.54  fof(f18,plain,(
% 1.45/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.54    inference(nnf_transformation,[],[f1])).
% 1.45/0.54  fof(f1,axiom,(
% 1.45/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.54  fof(f44,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK2),X0) | k6_subset_1(sK2,k7_relat_1(sK2,X1)) = k7_relat_1(sK2,k6_subset_1(X0,X1))) )),
% 1.45/0.54    inference(resolution,[],[f31,f21])).
% 1.45/0.54  fof(f31,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f14])).
% 1.45/0.54  fof(f14,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(flattening,[],[f13])).
% 1.45/0.54  fof(f13,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(ennf_transformation,[],[f6])).
% 1.45/0.54  fof(f6,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).
% 1.45/0.54  fof(f30,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f12])).
% 1.45/0.54  fof(f12,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(flattening,[],[f11])).
% 1.45/0.54  fof(f11,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(ennf_transformation,[],[f5])).
% 1.45/0.54  fof(f5,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f17])).
% 1.45/0.54  fof(f59,plain,(
% 1.45/0.54    ( ! [X0] : (r1_xboole_0(k6_subset_1(X0,sK1),sK0)) )),
% 1.45/0.54    inference(superposition,[],[f57,f42])).
% 1.45/0.54  fof(f42,plain,(
% 1.45/0.54    ( ! [X0] : (sK0 = k6_subset_1(sK0,k6_subset_1(X0,sK1))) )),
% 1.45/0.54    inference(resolution,[],[f38,f22])).
% 1.45/0.54  fof(f22,plain,(
% 1.45/0.54    r1_tarski(sK0,sK1)),
% 1.45/0.54    inference(cnf_transformation,[],[f17])).
% 1.45/0.54  fof(f38,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k6_subset_1(X0,k6_subset_1(X2,X1)) = X0) )),
% 1.45/0.54    inference(resolution,[],[f35,f34])).
% 1.45/0.54  fof(f34,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 1.45/0.54    inference(definition_unfolding,[],[f28,f24])).
% 1.45/0.54  fof(f24,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f4])).
% 1.45/0.54  fof(f4,axiom,(
% 1.45/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.45/0.54  fof(f28,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f20])).
% 1.45/0.54  fof(f20,plain,(
% 1.45/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.45/0.54    inference(nnf_transformation,[],[f2])).
% 1.45/0.54  fof(f2,axiom,(
% 1.45/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.45/0.54  fof(f35,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k6_subset_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.45/0.54    inference(definition_unfolding,[],[f32,f24])).
% 1.45/0.54  fof(f32,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  fof(f15,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f3])).
% 1.45/0.54  fof(f3,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.45/0.54  fof(f57,plain,(
% 1.45/0.54    ( ! [X4,X3] : (r1_xboole_0(X3,k6_subset_1(X4,X3))) )),
% 1.45/0.54    inference(trivial_inequality_removal,[],[f56])).
% 1.45/0.54  fof(f56,plain,(
% 1.45/0.54    ( ! [X4,X3] : (X3 != X3 | r1_xboole_0(X3,k6_subset_1(X4,X3))) )),
% 1.45/0.54    inference(superposition,[],[f33,f43])).
% 1.45/0.54  fof(f43,plain,(
% 1.45/0.54    ( ! [X2,X1] : (k6_subset_1(X1,k6_subset_1(X2,X1)) = X1) )),
% 1.45/0.54    inference(resolution,[],[f38,f36])).
% 1.45/0.54  fof(f33,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.45/0.54    inference(definition_unfolding,[],[f29,f24])).
% 1.45/0.54  fof(f29,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.45/0.54    inference(cnf_transformation,[],[f20])).
% 1.45/0.54  % SZS output end Proof for theBenchmark
% 1.45/0.54  % (29901)------------------------------
% 1.45/0.54  % (29901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (29901)Termination reason: Refutation
% 1.45/0.54  
% 1.45/0.54  % (29901)Memory used [KB]: 6268
% 1.45/0.54  % (29901)Time elapsed: 0.126 s
% 1.45/0.54  % (29901)------------------------------
% 1.45/0.54  % (29901)------------------------------
% 1.45/0.55  % (29878)Success in time 0.181 s
%------------------------------------------------------------------------------
