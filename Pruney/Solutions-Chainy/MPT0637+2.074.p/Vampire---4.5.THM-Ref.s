%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 175 expanded)
%              Number of leaves         :   15 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  118 ( 270 expanded)
%              Number of equality atoms :   66 ( 139 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f237])).

fof(f237,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f99,f192])).

fof(f192,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(forward_demodulation,[],[f172,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ) ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f172,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[],[f164,f138])).

fof(f138,plain,(
    ! [X6,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) = k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) ),
    inference(forward_demodulation,[],[f132,f35])).

fof(f35,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f132,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) = k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) ),
    inference(superposition,[],[f82,f103])).

fof(f103,plain,(
    ! [X4,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))),X4) ),
    inference(resolution,[],[f98,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f64,f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f46,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(backward_demodulation,[],[f55,f97])).

fof(f97,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f93,f38])).

fof(f93,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f56,f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f81,f58])).

fof(f58,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f44,f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f81,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f80,f58])).

fof(f80,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f77,f35])).

fof(f77,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f76,f36])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f73,f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f164,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(resolution,[],[f163,f36])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) ),
    inference(forward_demodulation,[],[f57,f97])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f99,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f61,f97])).

fof(f61,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f54,f58])).

fof(f54,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f34,f53])).

fof(f34,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32])).

fof(f32,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (5741)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (5739)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (5740)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (5753)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (5754)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (5741)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f237])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.47    inference(superposition,[],[f99,f192])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f172,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.47    inference(resolution,[],[f60,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.47    inference(resolution,[],[f49,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 0.21/0.47    inference(superposition,[],[f164,f138])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    ( ! [X6,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) = k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f132,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) = k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))))) )),
% 0.21/0.47    inference(superposition,[],[f82,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))),X4)) )),
% 0.21/0.47    inference(resolution,[],[f98,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.47    inference(resolution,[],[f64,f36])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(superposition,[],[f46,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f55,f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f93,f38])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) )),
% 0.21/0.47    inference(resolution,[],[f56,f36])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f45,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f42,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f43,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f41,f53])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f81,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.47    inference(resolution,[],[f44,f36])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f80,f58])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f77,f35])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f76,f36])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f73,f35])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) )),
% 0.21/0.47    inference(resolution,[],[f40,f36])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) )),
% 0.21/0.47    inference(resolution,[],[f163,f36])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f57,f97])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f51,f53])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 0.21/0.47    inference(backward_demodulation,[],[f61,f97])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.47    inference(backward_demodulation,[],[f54,f58])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.47    inference(definition_unfolding,[],[f34,f53])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f16])).
% 0.21/0.47  fof(f16,conjecture,(
% 0.21/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (5741)------------------------------
% 0.21/0.47  % (5741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5741)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (5741)Memory used [KB]: 6268
% 0.21/0.47  % (5741)Time elapsed: 0.067 s
% 0.21/0.47  % (5741)------------------------------
% 0.21/0.47  % (5741)------------------------------
% 0.21/0.47  % (5744)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (5738)Success in time 0.117 s
%------------------------------------------------------------------------------
