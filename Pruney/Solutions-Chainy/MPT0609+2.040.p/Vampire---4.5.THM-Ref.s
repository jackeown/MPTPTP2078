%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:30 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   30 (  67 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 ( 116 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f32])).

fof(f32,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f24,f29])).

fof(f29,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f27,f25])).

fof(f25,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) ),
    inference(resolution,[],[f20,f14])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(f27,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f26,f26])).

fof(f26,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f22,f14])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f17,f16,f16])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f24,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f15,f23])).

fof(f23,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f19,f14])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(f15,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.14/0.32  % Computer   : n016.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 10:21:49 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.34  ipcrm: permission denied for id (792035328)
% 0.14/0.34  ipcrm: permission denied for id (795770882)
% 0.14/0.35  ipcrm: permission denied for id (792068101)
% 0.14/0.35  ipcrm: permission denied for id (792100870)
% 0.14/0.35  ipcrm: permission denied for id (792133639)
% 0.14/0.35  ipcrm: permission denied for id (792166408)
% 0.14/0.35  ipcrm: permission denied for id (792199177)
% 0.14/0.35  ipcrm: permission denied for id (792264715)
% 0.14/0.36  ipcrm: permission denied for id (792330253)
% 0.14/0.36  ipcrm: permission denied for id (792395792)
% 0.14/0.36  ipcrm: permission denied for id (792461331)
% 0.14/0.37  ipcrm: permission denied for id (796098581)
% 0.14/0.37  ipcrm: permission denied for id (796131350)
% 0.14/0.37  ipcrm: permission denied for id (796196888)
% 0.14/0.37  ipcrm: permission denied for id (796295193)
% 0.14/0.37  ipcrm: permission denied for id (796262426)
% 0.14/0.38  ipcrm: permission denied for id (792723484)
% 0.14/0.38  ipcrm: permission denied for id (796360733)
% 0.14/0.38  ipcrm: permission denied for id (792789022)
% 0.19/0.39  ipcrm: permission denied for id (796557348)
% 0.19/0.39  ipcrm: permission denied for id (796590117)
% 0.19/0.39  ipcrm: permission denied for id (793083943)
% 0.19/0.39  ipcrm: permission denied for id (793116712)
% 0.19/0.39  ipcrm: permission denied for id (793149481)
% 0.19/0.39  ipcrm: permission denied for id (793182250)
% 0.19/0.40  ipcrm: permission denied for id (793215019)
% 0.19/0.40  ipcrm: permission denied for id (793247788)
% 0.19/0.40  ipcrm: permission denied for id (793280557)
% 0.19/0.40  ipcrm: permission denied for id (793313326)
% 0.19/0.40  ipcrm: permission denied for id (793346096)
% 0.19/0.40  ipcrm: permission denied for id (793378865)
% 0.19/0.40  ipcrm: permission denied for id (793411634)
% 0.19/0.41  ipcrm: permission denied for id (793444403)
% 0.19/0.41  ipcrm: permission denied for id (793477172)
% 0.19/0.41  ipcrm: permission denied for id (793509941)
% 0.19/0.41  ipcrm: permission denied for id (793542710)
% 0.19/0.41  ipcrm: permission denied for id (796688439)
% 0.19/0.41  ipcrm: permission denied for id (793608249)
% 0.19/0.41  ipcrm: permission denied for id (793641018)
% 0.19/0.42  ipcrm: permission denied for id (793706556)
% 0.19/0.42  ipcrm: permission denied for id (796885056)
% 0.19/0.43  ipcrm: permission denied for id (796983363)
% 0.19/0.43  ipcrm: permission denied for id (797048901)
% 0.19/0.43  ipcrm: permission denied for id (797114439)
% 0.19/0.43  ipcrm: permission denied for id (797179977)
% 0.19/0.44  ipcrm: permission denied for id (797245515)
% 0.19/0.44  ipcrm: permission denied for id (797278284)
% 0.19/0.44  ipcrm: permission denied for id (797311053)
% 0.19/0.44  ipcrm: permission denied for id (797343822)
% 0.19/0.44  ipcrm: permission denied for id (797409360)
% 0.19/0.45  ipcrm: permission denied for id (797507667)
% 0.19/0.45  ipcrm: permission denied for id (794394709)
% 0.19/0.45  ipcrm: permission denied for id (797573206)
% 0.19/0.45  ipcrm: permission denied for id (797671513)
% 0.19/0.45  ipcrm: permission denied for id (797704282)
% 0.19/0.46  ipcrm: permission denied for id (797737051)
% 0.19/0.46  ipcrm: permission denied for id (794689630)
% 0.19/0.46  ipcrm: permission denied for id (797835359)
% 0.19/0.46  ipcrm: permission denied for id (794755168)
% 0.19/0.46  ipcrm: permission denied for id (797868129)
% 0.19/0.46  ipcrm: permission denied for id (794787938)
% 0.19/0.47  ipcrm: permission denied for id (794820707)
% 0.19/0.47  ipcrm: permission denied for id (794853476)
% 0.19/0.47  ipcrm: permission denied for id (794886245)
% 0.19/0.47  ipcrm: permission denied for id (794919014)
% 0.19/0.47  ipcrm: permission denied for id (794951783)
% 0.19/0.47  ipcrm: permission denied for id (794984552)
% 0.19/0.47  ipcrm: permission denied for id (797900905)
% 0.19/0.47  ipcrm: permission denied for id (795017322)
% 0.19/0.47  ipcrm: permission denied for id (795050091)
% 0.19/0.48  ipcrm: permission denied for id (795082860)
% 0.19/0.48  ipcrm: permission denied for id (795115629)
% 0.19/0.48  ipcrm: permission denied for id (795148398)
% 0.19/0.48  ipcrm: permission denied for id (795181167)
% 0.19/0.49  ipcrm: permission denied for id (798130293)
% 0.19/0.49  ipcrm: permission denied for id (798195831)
% 0.19/0.49  ipcrm: permission denied for id (795476088)
% 0.19/0.49  ipcrm: permission denied for id (795508857)
% 0.19/0.49  ipcrm: permission denied for id (795541626)
% 0.19/0.49  ipcrm: permission denied for id (795574395)
% 0.19/0.50  ipcrm: permission denied for id (795607164)
% 0.87/0.60  % (18617)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.87/0.61  % (18617)Refutation found. Thanks to Tanya!
% 0.87/0.61  % SZS status Theorem for theBenchmark
% 0.87/0.61  % (18615)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.87/0.61  % (18627)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.87/0.62  % SZS output start Proof for theBenchmark
% 0.87/0.62  fof(f35,plain,(
% 0.87/0.62    $false),
% 0.87/0.62    inference(trivial_inequality_removal,[],[f32])).
% 0.87/0.62  fof(f32,plain,(
% 0.87/0.62    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 0.87/0.62    inference(superposition,[],[f24,f29])).
% 0.87/0.62  fof(f29,plain,(
% 0.87/0.62    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.87/0.62    inference(forward_demodulation,[],[f27,f25])).
% 0.87/0.62  fof(f25,plain,(
% 0.87/0.62    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)))) )),
% 0.87/0.62    inference(resolution,[],[f20,f14])).
% 0.87/0.62  fof(f14,plain,(
% 0.87/0.62    v1_relat_1(sK1)),
% 0.87/0.62    inference(cnf_transformation,[],[f13])).
% 0.87/0.62  fof(f13,plain,(
% 0.87/0.62    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.87/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 0.87/0.62  fof(f12,plain,(
% 0.87/0.62    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.87/0.62    introduced(choice_axiom,[])).
% 0.87/0.62  fof(f8,plain,(
% 0.87/0.62    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.87/0.62    inference(ennf_transformation,[],[f7])).
% 0.87/0.62  fof(f7,negated_conjecture,(
% 0.87/0.62    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.87/0.62    inference(negated_conjecture,[],[f6])).
% 0.87/0.62  fof(f6,conjecture,(
% 0.87/0.62    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).
% 0.87/0.62  fof(f20,plain,(
% 0.87/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))) )),
% 0.87/0.62    inference(cnf_transformation,[],[f11])).
% 0.87/0.62  fof(f11,plain,(
% 0.87/0.62    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 0.87/0.62    inference(ennf_transformation,[],[f3])).
% 0.87/0.62  fof(f3,axiom,(
% 0.87/0.62    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 0.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).
% 0.87/0.62  fof(f27,plain,(
% 0.87/0.62    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.87/0.62    inference(superposition,[],[f26,f26])).
% 0.87/0.63  fof(f26,plain,(
% 0.87/0.63    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X0))) )),
% 0.87/0.63    inference(resolution,[],[f22,f14])).
% 0.87/0.63  fof(f22,plain,(
% 0.87/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0))) )),
% 0.87/0.63    inference(definition_unfolding,[],[f18,f21])).
% 0.87/0.63  fof(f21,plain,(
% 0.87/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.87/0.63    inference(definition_unfolding,[],[f17,f16,f16])).
% 0.87/0.63  fof(f16,plain,(
% 0.87/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.87/0.63    inference(cnf_transformation,[],[f2])).
% 0.87/0.63  fof(f2,axiom,(
% 0.87/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.87/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.87/0.63  fof(f17,plain,(
% 0.87/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.87/0.63    inference(cnf_transformation,[],[f1])).
% 0.87/0.63  fof(f1,axiom,(
% 0.87/0.63    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.87/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.87/0.63  fof(f18,plain,(
% 0.87/0.63    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.87/0.63    inference(cnf_transformation,[],[f9])).
% 0.87/0.63  fof(f9,plain,(
% 0.87/0.63    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.87/0.63    inference(ennf_transformation,[],[f5])).
% 0.87/0.63  fof(f5,axiom,(
% 0.87/0.63    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.87/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.87/0.63  fof(f24,plain,(
% 0.87/0.63    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 0.87/0.63    inference(backward_demodulation,[],[f15,f23])).
% 0.87/0.63  fof(f23,plain,(
% 0.87/0.63    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0)))) )),
% 0.87/0.63    inference(resolution,[],[f19,f14])).
% 0.87/0.63  fof(f19,plain,(
% 0.87/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))) )),
% 0.87/0.63    inference(cnf_transformation,[],[f10])).
% 0.87/0.63  fof(f10,plain,(
% 0.87/0.63    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.87/0.63    inference(ennf_transformation,[],[f4])).
% 0.87/0.63  fof(f4,axiom,(
% 0.87/0.63    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 0.87/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).
% 0.87/0.63  fof(f15,plain,(
% 0.87/0.63    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.87/0.63    inference(cnf_transformation,[],[f13])).
% 0.87/0.63  % SZS output end Proof for theBenchmark
% 0.87/0.63  % (18617)------------------------------
% 0.87/0.63  % (18617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.87/0.63  % (18617)Termination reason: Refutation
% 0.87/0.63  
% 0.87/0.63  % (18617)Memory used [KB]: 6140
% 0.87/0.63  % (18617)Time elapsed: 0.042 s
% 0.87/0.63  % (18617)------------------------------
% 0.87/0.63  % (18617)------------------------------
% 0.87/0.63  % (18616)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.87/0.63  % (18454)Success in time 0.292 s
%------------------------------------------------------------------------------
