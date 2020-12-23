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
% DateTime   : Thu Dec  3 12:53:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  97 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 215 expanded)
%              Number of equality atoms :   43 (  92 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f44,f73])).

fof(f73,plain,(
    ! [X1] : k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f72,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

% (7536)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f12,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f72,plain,(
    ! [X1] :
      ( k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f71,f23])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X1] :
      ( k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0) ),
    inference(superposition,[],[f45,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f26,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(resolution,[],[f39,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

% (7534)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f68,plain,(
    ! [X1] :
      ( k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1))
      | ~ r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))),k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f30,f57])).

fof(f57,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK1)))) ),
    inference(superposition,[],[f56,f37])).

fof(f56,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k1_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),X0))) ),
    inference(resolution,[],[f38,f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f44,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f43,f22])).

fof(f43,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f36,f25])).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f36,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k1_enumset1(sK0,sK0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f24,f35])).

fof(f24,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (7556)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (7548)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (7548)Refutation not found, incomplete strategy% (7548)------------------------------
% 0.21/0.50  % (7548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7539)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (7533)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (7548)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7548)Memory used [KB]: 1663
% 0.21/0.50  % (7548)Time elapsed: 0.057 s
% 0.21/0.50  % (7548)------------------------------
% 0.21/0.50  % (7548)------------------------------
% 0.21/0.51  % (7535)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (7556)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 0.21/0.51    inference(superposition,[],[f44,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X1] : (k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f72,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  % (7536)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X1] : (k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X1] : (k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0)) )),
% 0.21/0.51    inference(superposition,[],[f45,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f26,f27,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.21/0.51    inference(resolution,[],[f39,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  % (7534)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f34,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f28,f27])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X1] : (k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1)) | ~r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(sK1))),k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.51    inference(superposition,[],[f30,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK1))))) )),
% 0.21/0.51    inference(superposition,[],[f56,f37])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k1_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),X0)))) )),
% 0.21/0.51    inference(resolution,[],[f38,f22])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f29,f35])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f43,f22])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK1))) | ~v1_relat_1(sK1)),
% 0.21/0.51    inference(superposition,[],[f36,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k1_setfam_1(k1_enumset1(sK0,sK0,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 0.21/0.51    inference(definition_unfolding,[],[f24,f35])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (7556)------------------------------
% 0.21/0.51  % (7556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7556)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (7556)Memory used [KB]: 6268
% 0.21/0.51  % (7556)Time elapsed: 0.059 s
% 0.21/0.51  % (7556)------------------------------
% 0.21/0.51  % (7556)------------------------------
% 0.21/0.51  % (7558)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (7529)Success in time 0.152 s
%------------------------------------------------------------------------------
