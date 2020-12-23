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
% DateTime   : Thu Dec  3 12:54:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 387 expanded)
%              Number of leaves         :   10 ( 111 expanded)
%              Depth                    :   18
%              Number of atoms          :  138 (1134 expanded)
%              Number of equality atoms :   48 ( 216 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f677,plain,(
    $false ),
    inference(resolution,[],[f661,f28])).

fof(f28,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f661,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f55,f630])).

fof(f630,plain,(
    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(resolution,[],[f608,f47])).

fof(f47,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1 ) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f608,plain,(
    r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(superposition,[],[f55,f600])).

fof(f600,plain,(
    sK0 = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f599,f65])).

fof(f65,plain,(
    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2))) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f599,plain,(
    k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2))) = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f598,f362])).

fof(f362,plain,(
    ! [X1] : k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK2))) ),
    inference(superposition,[],[f325,f320])).

fof(f320,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2))))) ),
    inference(superposition,[],[f145,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f38,f38])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f145,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) ),
    inference(resolution,[],[f141,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) ) ),
    inference(resolution,[],[f71,f25])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X2)) = k9_relat_1(X1,k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X2))))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f29,f41])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f325,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2))))) ),
    inference(superposition,[],[f145,f242])).

fof(f242,plain,(
    ! [X2,X3] : k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X2,X2,X3))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X3,X3,X2))) ),
    inference(superposition,[],[f80,f79])).

fof(f79,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f76,f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) ),
    inference(resolution,[],[f42,f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f35,f39,f39])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(f80,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X1),k10_relat_1(sK2,X1),k10_relat_1(sK2,X0))) ),
    inference(superposition,[],[f79,f43])).

fof(f598,plain,(
    k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),sK0)) = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f570,f145])).

fof(f570,plain,(
    k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),sK0)))) ),
    inference(superposition,[],[f145,f88])).

fof(f88,plain,(
    ! [X0] : k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,sK0))) ),
    inference(forward_demodulation,[],[f86,f79])).

fof(f86,plain,(
    ! [X0] : k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f79,f82])).

fof(f82,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(superposition,[],[f79,f64])).

fof(f64,plain,(
    k10_relat_1(sK2,sK0) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f40,f26])).

fof(f26,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0) ),
    inference(superposition,[],[f41,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:18:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (16214)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (16215)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (16217)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (16219)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (16218)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (16213)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (16232)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (16222)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (16238)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (16223)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (16235)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (16228)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (16216)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (16236)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (16240)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (16241)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (16229)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (16220)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (16237)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (16242)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (16242)Refutation not found, incomplete strategy% (16242)------------------------------
% 0.22/0.55  % (16242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16242)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16242)Memory used [KB]: 1663
% 0.22/0.55  % (16242)Time elapsed: 0.002 s
% 0.22/0.55  % (16242)------------------------------
% 0.22/0.55  % (16242)------------------------------
% 0.22/0.55  % (16239)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (16226)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (16234)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (16225)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (16223)Refutation not found, incomplete strategy% (16223)------------------------------
% 0.22/0.55  % (16223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16223)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16223)Memory used [KB]: 10746
% 0.22/0.55  % (16223)Time elapsed: 0.149 s
% 0.22/0.55  % (16223)------------------------------
% 0.22/0.55  % (16223)------------------------------
% 0.22/0.55  % (16230)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (16231)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (16241)Refutation not found, incomplete strategy% (16241)------------------------------
% 0.22/0.55  % (16241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16241)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16241)Memory used [KB]: 10746
% 0.22/0.55  % (16241)Time elapsed: 0.150 s
% 0.22/0.55  % (16241)------------------------------
% 0.22/0.55  % (16241)------------------------------
% 0.22/0.56  % (16221)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (16224)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (16227)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (16229)Refutation not found, incomplete strategy% (16229)------------------------------
% 0.22/0.56  % (16229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (16229)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (16229)Memory used [KB]: 10618
% 0.22/0.56  % (16229)Time elapsed: 0.159 s
% 0.22/0.56  % (16229)------------------------------
% 0.22/0.56  % (16229)------------------------------
% 0.22/0.56  % (16233)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (16218)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f677,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(resolution,[],[f661,f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.57    inference(flattening,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.57    inference(negated_conjecture,[],[f11])).
% 0.22/0.57  fof(f11,conjecture,(
% 0.22/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.22/0.57  fof(f661,plain,(
% 0.22/0.57    r1_tarski(sK0,sK1)),
% 0.22/0.57    inference(superposition,[],[f55,f630])).
% 0.22/0.57  fof(f630,plain,(
% 0.22/0.57    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.22/0.57    inference(resolution,[],[f608,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X2,X1] : (~r1_tarski(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) | k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1) )),
% 0.22/0.57    inference(resolution,[],[f32,f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f34,f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f37,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(flattening,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f608,plain,(
% 0.22/0.57    r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 0.22/0.57    inference(superposition,[],[f55,f600])).
% 0.22/0.57  fof(f600,plain,(
% 0.22/0.57    sK0 = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))),
% 0.22/0.57    inference(forward_demodulation,[],[f599,f65])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2)))),
% 0.22/0.57    inference(resolution,[],[f40,f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 0.22/0.57    inference(definition_unfolding,[],[f33,f39])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.57  fof(f599,plain,(
% 0.22/0.57    k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2))) = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))),
% 0.22/0.57    inference(forward_demodulation,[],[f598,f362])).
% 0.22/0.57  fof(f362,plain,(
% 0.22/0.57    ( ! [X1] : (k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK2)))) )),
% 0.22/0.57    inference(superposition,[],[f325,f320])).
% 0.22/0.57  fof(f320,plain,(
% 0.22/0.57    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2)))))) )),
% 0.22/0.57    inference(superposition,[],[f145,f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f36,f38,f38])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.57  fof(f145,plain,(
% 0.22/0.57    ( ! [X0] : (k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0))))) )),
% 0.22/0.57    inference(resolution,[],[f141,f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    v1_relat_1(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f141,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_relat_1(sK2) | k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0))))) )),
% 0.22/0.57    inference(resolution,[],[f71,f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    v1_funct_1(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ( ! [X2,X1] : (~v1_funct_1(X1) | k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X2)) = k9_relat_1(X1,k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X2)))) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(resolution,[],[f29,f41])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(flattening,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.22/0.57  fof(f325,plain,(
% 0.22/0.57    ( ! [X0] : (k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK2)))))) )),
% 0.22/0.57    inference(superposition,[],[f145,f242])).
% 0.22/0.57  fof(f242,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X2,X2,X3))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X3,X3,X2)))) )),
% 0.22/0.57    inference(superposition,[],[f80,f79])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))) )),
% 0.22/0.57    inference(resolution,[],[f76,f24])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(sK2) | k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))) )),
% 0.22/0.57    inference(resolution,[],[f42,f25])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f35,f39,f39])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.57    inference(flattening,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X1),k10_relat_1(sK2,X1),k10_relat_1(sK2,X0)))) )),
% 0.22/0.57    inference(superposition,[],[f79,f43])).
% 0.22/0.57  fof(f598,plain,(
% 0.22/0.57    k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),sK0)) = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))),
% 0.22/0.57    inference(forward_demodulation,[],[f570,f145])).
% 0.22/0.57  fof(f570,plain,(
% 0.22/0.57    k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),sK0))))),
% 0.22/0.57    inference(superposition,[],[f145,f88])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ( ! [X0] : (k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,sK0)))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f86,f79])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    ( ! [X0] : (k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))))) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0)))) )),
% 0.22/0.57    inference(superposition,[],[f79,f82])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 0.22/0.57    inference(superposition,[],[f79,f64])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    k10_relat_1(sK2,sK0) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 0.22/0.57    inference(resolution,[],[f40,f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0)) )),
% 0.22/0.57    inference(superposition,[],[f41,f43])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (16218)------------------------------
% 0.22/0.57  % (16218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (16218)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (16218)Memory used [KB]: 2174
% 0.22/0.57  % (16218)Time elapsed: 0.145 s
% 0.22/0.57  % (16218)------------------------------
% 0.22/0.57  % (16218)------------------------------
% 0.22/0.57  % (16212)Success in time 0.207 s
%------------------------------------------------------------------------------
