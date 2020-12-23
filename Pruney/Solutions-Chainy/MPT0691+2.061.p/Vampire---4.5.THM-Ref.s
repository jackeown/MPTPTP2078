%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:53 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 208 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  153 ( 410 expanded)
%              Number of equality atoms :   72 ( 148 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(subsumption_resolution,[],[f261,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f91,f65])).

fof(f65,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(unit_resulting_resolution,[],[f69,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f261,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f180,f207])).

fof(f207,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f206,f76])).

fof(f76,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f36,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

% (23705)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (23701)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (23704)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (23697)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (23701)Refutation not found, incomplete strategy% (23701)------------------------------
% (23701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23701)Termination reason: Refutation not found, incomplete strategy

% (23701)Memory used [KB]: 1791
% (23701)Time elapsed: 0.164 s
% (23701)------------------------------
% (23701)------------------------------
% (23687)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (23685)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (23698)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (23693)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (23706)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (23696)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f206,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f205,f71])).

fof(f71,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

% (23703)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f205,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f38,f153])).

fof(f153,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f146,f83])).

fof(f83,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(unit_resulting_resolution,[],[f35,f69,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f146,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f35,f36,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(k7_relat_1(X0,X1),X1)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f77,f45])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(k7_relat_1(X0,X1),X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f46])).

fof(f39,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f180,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f96,f99])).

fof(f99,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1))) ),
    inference(unit_resulting_resolution,[],[f35,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f53,f63])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f96,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ),
    inference(unit_resulting_resolution,[],[f37,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:01:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (23692)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (23689)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (23700)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (23684)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.56  % (23688)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.56/0.57  % (23690)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.58  % (23700)Refutation not found, incomplete strategy% (23700)------------------------------
% 1.56/0.58  % (23700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (23700)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (23700)Memory used [KB]: 10618
% 1.56/0.58  % (23700)Time elapsed: 0.152 s
% 1.56/0.58  % (23700)------------------------------
% 1.56/0.58  % (23700)------------------------------
% 1.56/0.58  % (23686)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.59  % (23688)Refutation found. Thanks to Tanya!
% 1.56/0.59  % SZS status Theorem for theBenchmark
% 1.56/0.59  % SZS output start Proof for theBenchmark
% 1.56/0.59  fof(f266,plain,(
% 1.56/0.59    $false),
% 1.56/0.59    inference(subsumption_resolution,[],[f261,f94])).
% 1.56/0.59  fof(f94,plain,(
% 1.56/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.56/0.59    inference(forward_demodulation,[],[f91,f65])).
% 1.56/0.59  fof(f65,plain,(
% 1.56/0.59    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.56/0.59    inference(definition_unfolding,[],[f41,f63])).
% 1.56/0.59  fof(f63,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.56/0.59    inference(definition_unfolding,[],[f42,f62])).
% 1.56/0.59  fof(f62,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.56/0.59    inference(definition_unfolding,[],[f43,f61])).
% 1.56/0.59  fof(f61,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.56/0.59    inference(definition_unfolding,[],[f52,f60])).
% 1.56/0.59  fof(f60,plain,(
% 1.56/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.56/0.59    inference(definition_unfolding,[],[f54,f59])).
% 1.56/0.59  fof(f59,plain,(
% 1.56/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.56/0.59    inference(definition_unfolding,[],[f55,f58])).
% 1.56/0.59  fof(f58,plain,(
% 1.56/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.56/0.59    inference(definition_unfolding,[],[f56,f57])).
% 1.56/0.59  fof(f57,plain,(
% 1.56/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f10])).
% 1.56/0.59  fof(f10,axiom,(
% 1.56/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.56/0.59  fof(f56,plain,(
% 1.56/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f9])).
% 1.56/0.59  fof(f9,axiom,(
% 1.56/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.56/0.59  fof(f55,plain,(
% 1.56/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f8])).
% 1.56/0.59  fof(f8,axiom,(
% 1.56/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.56/0.59  fof(f54,plain,(
% 1.56/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f7])).
% 1.56/0.59  fof(f7,axiom,(
% 1.56/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.56/0.59  fof(f52,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f6])).
% 1.56/0.59  fof(f6,axiom,(
% 1.56/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.59  fof(f43,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f5])).
% 1.56/0.59  fof(f5,axiom,(
% 1.56/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.59  fof(f42,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.56/0.59    inference(cnf_transformation,[],[f11])).
% 1.56/0.59  fof(f11,axiom,(
% 1.56/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.56/0.59  fof(f41,plain,(
% 1.56/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.56/0.59    inference(cnf_transformation,[],[f20])).
% 1.56/0.59  fof(f20,plain,(
% 1.56/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.56/0.59    inference(rectify,[],[f1])).
% 1.56/0.59  fof(f1,axiom,(
% 1.56/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.56/0.59  fof(f91,plain,(
% 1.56/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.56/0.59    inference(unit_resulting_resolution,[],[f69,f66])).
% 1.56/0.59  fof(f66,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 1.56/0.59    inference(definition_unfolding,[],[f51,f64])).
% 1.56/0.59  fof(f64,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.56/0.59    inference(definition_unfolding,[],[f44,f63])).
% 1.56/0.59  fof(f44,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.56/0.59    inference(cnf_transformation,[],[f4])).
% 1.56/0.59  fof(f4,axiom,(
% 1.56/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.56/0.59  fof(f51,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f34])).
% 1.56/0.59  fof(f34,plain,(
% 1.56/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.56/0.59    inference(nnf_transformation,[],[f3])).
% 1.56/0.59  fof(f3,axiom,(
% 1.56/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.56/0.59  fof(f69,plain,(
% 1.56/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.59    inference(equality_resolution,[],[f48])).
% 1.56/0.59  fof(f48,plain,(
% 1.56/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.59    inference(cnf_transformation,[],[f33])).
% 1.56/0.59  fof(f33,plain,(
% 1.56/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.59    inference(flattening,[],[f32])).
% 1.56/0.59  fof(f32,plain,(
% 1.56/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.59    inference(nnf_transformation,[],[f2])).
% 1.56/0.59  fof(f2,axiom,(
% 1.56/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.59  fof(f261,plain,(
% 1.56/0.59    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 1.56/0.59    inference(backward_demodulation,[],[f180,f207])).
% 1.56/0.59  fof(f207,plain,(
% 1.56/0.59    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 1.56/0.59    inference(forward_demodulation,[],[f206,f76])).
% 1.56/0.59  fof(f76,plain,(
% 1.56/0.59    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.56/0.59    inference(unit_resulting_resolution,[],[f35,f36,f46])).
% 1.56/0.59  fof(f46,plain,(
% 1.56/0.59    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f28])).
% 1.56/0.59  fof(f28,plain,(
% 1.56/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.56/0.59    inference(flattening,[],[f27])).
% 1.56/0.59  fof(f27,plain,(
% 1.56/0.59    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.56/0.59    inference(ennf_transformation,[],[f16])).
% 1.56/0.59  fof(f16,axiom,(
% 1.56/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.56/0.59  fof(f36,plain,(
% 1.56/0.59    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.56/0.59    inference(cnf_transformation,[],[f31])).
% 1.56/0.59  fof(f31,plain,(
% 1.56/0.59    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.56/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f30])).
% 1.56/0.59  fof(f30,plain,(
% 1.56/0.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  % (23705)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.73/0.59  % (23701)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.73/0.59  % (23704)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.73/0.59  % (23697)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.73/0.59  % (23701)Refutation not found, incomplete strategy% (23701)------------------------------
% 1.73/0.59  % (23701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (23701)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (23701)Memory used [KB]: 1791
% 1.73/0.59  % (23701)Time elapsed: 0.164 s
% 1.73/0.59  % (23701)------------------------------
% 1.73/0.59  % (23701)------------------------------
% 1.73/0.60  % (23687)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.73/0.60  % (23685)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.73/0.60  % (23698)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.73/0.60  % (23693)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.73/0.61  % (23706)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.73/0.61  % (23696)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.73/0.61  fof(f22,plain,(
% 1.73/0.61    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.73/0.61    inference(flattening,[],[f21])).
% 1.73/0.61  fof(f21,plain,(
% 1.73/0.61    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f19])).
% 1.73/0.61  fof(f19,negated_conjecture,(
% 1.73/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.73/0.61    inference(negated_conjecture,[],[f18])).
% 1.73/0.61  fof(f18,conjecture,(
% 1.73/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.73/0.61  fof(f35,plain,(
% 1.73/0.61    v1_relat_1(sK1)),
% 1.73/0.61    inference(cnf_transformation,[],[f31])).
% 1.73/0.61  fof(f206,plain,(
% 1.73/0.61    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 1.73/0.61    inference(subsumption_resolution,[],[f205,f71])).
% 1.73/0.61  fof(f71,plain,(
% 1.73/0.61    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f35,f45])).
% 1.73/0.61  fof(f45,plain,(
% 1.73/0.61    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f26])).
% 1.73/0.61  % (23703)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.73/0.61  fof(f26,plain,(
% 1.73/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.73/0.61    inference(ennf_transformation,[],[f12])).
% 1.73/0.61  fof(f12,axiom,(
% 1.73/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.73/0.61  fof(f205,plain,(
% 1.73/0.61    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.73/0.61    inference(superposition,[],[f38,f153])).
% 1.73/0.61  fof(f153,plain,(
% 1.73/0.61    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 1.73/0.61    inference(forward_demodulation,[],[f146,f83])).
% 1.73/0.61  fof(f83,plain,(
% 1.73/0.61    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f35,f69,f40])).
% 1.73/0.61  fof(f40,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f25])).
% 1.73/0.61  fof(f25,plain,(
% 1.73/0.61    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.73/0.61    inference(ennf_transformation,[],[f14])).
% 1.73/0.61  fof(f14,axiom,(
% 1.73/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 1.73/0.61  fof(f146,plain,(
% 1.73/0.61    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f35,f36,f78])).
% 1.73/0.61  fof(f78,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(k7_relat_1(X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.73/0.61    inference(subsumption_resolution,[],[f77,f45])).
% 1.73/0.61  fof(f77,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.73/0.61    inference(superposition,[],[f39,f46])).
% 1.73/0.61  fof(f39,plain,(
% 1.73/0.61    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f24])).
% 1.73/0.61  fof(f24,plain,(
% 1.73/0.61    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.61    inference(ennf_transformation,[],[f13])).
% 1.73/0.61  fof(f13,axiom,(
% 1.73/0.61    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.73/0.61  fof(f38,plain,(
% 1.73/0.61    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f23])).
% 1.73/0.61  fof(f23,plain,(
% 1.73/0.61    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.73/0.61    inference(ennf_transformation,[],[f15])).
% 1.73/0.61  fof(f15,axiom,(
% 1.73/0.61    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.73/0.61  fof(f180,plain,(
% 1.73/0.61    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))),
% 1.73/0.61    inference(backward_demodulation,[],[f96,f99])).
% 1.73/0.61  fof(f99,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1)))) )),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f35,f68])).
% 1.73/0.61  fof(f68,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 1.73/0.61    inference(definition_unfolding,[],[f53,f63])).
% 1.73/0.61  fof(f53,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f29])).
% 1.73/0.61  fof(f29,plain,(
% 1.73/0.61    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.73/0.61    inference(ennf_transformation,[],[f17])).
% 1.73/0.61  fof(f17,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.73/0.61  fof(f96,plain,(
% 1.73/0.61    k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f37,f67])).
% 1.73/0.61  fof(f67,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 1.73/0.61    inference(definition_unfolding,[],[f50,f64])).
% 1.73/0.61  fof(f50,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f34])).
% 1.73/0.61  fof(f37,plain,(
% 1.73/0.61    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.73/0.61    inference(cnf_transformation,[],[f31])).
% 1.73/0.61  % SZS output end Proof for theBenchmark
% 1.73/0.61  % (23688)------------------------------
% 1.73/0.61  % (23688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (23688)Termination reason: Refutation
% 1.73/0.61  
% 1.73/0.61  % (23688)Memory used [KB]: 1918
% 1.73/0.61  % (23688)Time elapsed: 0.141 s
% 1.73/0.61  % (23688)------------------------------
% 1.73/0.61  % (23688)------------------------------
% 1.73/0.61  % (23699)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.73/0.61  % (23683)Success in time 0.243 s
%------------------------------------------------------------------------------
