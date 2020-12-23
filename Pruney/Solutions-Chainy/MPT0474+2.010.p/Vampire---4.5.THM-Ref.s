%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 104 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :   87 ( 154 expanded)
%              Number of equality atoms :   61 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f28])).

fof(f28,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f18])).

fof(f18,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

fof(f59,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f58,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f58,plain,(
    k1_xboole_0 = k4_relat_1(k6_subset_1(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f57,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f49,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k6_subset_1(X0,X0) ),
    inference(superposition,[],[f46,f48])).

fof(f48,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f32,f43])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    k4_relat_1(k6_subset_1(k1_xboole_0,k1_xboole_0)) = k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k4_relat_1(k6_subset_1(k1_xboole_0,k1_xboole_0)) = k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f55,f45])).

fof(f55,plain,(
    ! [X0] :
      ( k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0
      | k4_relat_1(k6_subset_1(X0,k1_xboole_0)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0)) ) ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k4_relat_1(k6_subset_1(X0,k1_xboole_0)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0))
      | k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0 ) ),
    inference(superposition,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X1,k2_enumset1(sK0(X1),sK0(X1),sK0(X1),sK0(X1))) != X1
      | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0 ) ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0 ) ),
    inference(resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k6_subset_1(X0,k2_enumset1(X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f36,f32,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
     => ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0
      | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ),
    inference(resolution,[],[f51,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (24230)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (24233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (24246)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (24234)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (24234)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f59,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,negated_conjecture,(
% 0.20/0.51    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(negated_conjecture,[],[f17])).
% 0.20/0.51  fof(f17,conjecture,(
% 0.20/0.51    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(forward_demodulation,[],[f58,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f31,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    k1_xboole_0 = k4_relat_1(k6_subset_1(k1_xboole_0,k1_xboole_0))),
% 0.20/0.51    inference(forward_demodulation,[],[f57,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f49,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k6_subset_1(X0,X0)) )),
% 0.20/0.51    inference(superposition,[],[f46,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f38,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f37,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f40,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.51    inference(rectify,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f35,f32,f43])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k4_relat_1(k6_subset_1(k1_xboole_0,k1_xboole_0)) = k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | k4_relat_1(k6_subset_1(k1_xboole_0,k1_xboole_0)) = k6_subset_1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))),
% 0.20/0.51    inference(superposition,[],[f55,f45])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0] : (k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0 | k4_relat_1(k6_subset_1(X0,k1_xboole_0)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0))) )),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k4_relat_1(k6_subset_1(X0,k1_xboole_0)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0)) | k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0) )),
% 0.20/0.51    inference(superposition,[],[f53,f45])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k6_subset_1(X1,k2_enumset1(sK0(X1),sK0(X1),sK0(X1),sK0(X1))) != X1 | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0) )),
% 0.20/0.51    inference(resolution,[],[f52,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(X0) | k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0) )),
% 0.20/0.51    inference(resolution,[],[f47,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.20/0.51    inference(unused_predicate_definition_removal,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k6_subset_1(X0,k2_enumset1(X1,X1,X1,X1)) != X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f36,f32,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f39,f42])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 => ~r2_hidden(X1,X0))),
% 0.20/0.51    inference(unused_predicate_definition_removal,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k6_subset_1(X0,k2_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0))) != X0 | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))) )),
% 0.20/0.51    inference(resolution,[],[f51,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_relat_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (24234)------------------------------
% 0.20/0.51  % (24234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24234)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (24234)Memory used [KB]: 6268
% 0.20/0.51  % (24234)Time elapsed: 0.108 s
% 0.20/0.51  % (24234)------------------------------
% 0.20/0.51  % (24234)------------------------------
% 0.20/0.51  % (24248)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (24232)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (24243)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (24237)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (24253)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (24253)Refutation not found, incomplete strategy% (24253)------------------------------
% 0.20/0.51  % (24253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24253)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24253)Memory used [KB]: 1663
% 0.20/0.51  % (24253)Time elapsed: 0.113 s
% 0.20/0.51  % (24253)------------------------------
% 0.20/0.51  % (24253)------------------------------
% 0.20/0.51  % (24228)Success in time 0.156 s
%------------------------------------------------------------------------------
