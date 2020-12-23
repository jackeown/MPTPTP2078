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
% DateTime   : Thu Dec  3 12:48:26 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   90 (1048 expanded)
%              Number of leaves         :   18 ( 333 expanded)
%              Depth                    :   21
%              Number of atoms          :  161 (1354 expanded)
%              Number of equality atoms :   72 ( 944 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(subsumption_resolution,[],[f304,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f304,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f290,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f290,plain,(
    ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(global_subsumption,[],[f28,f289,f287])).

fof(f287,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f278])).

fof(f278,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f31,f252])).

fof(f252,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f245,f164])).

fof(f164,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f163,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X0,X1))
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f83,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f34,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X0,X1))
      | k1_xboole_0 != k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X2))) ) ),
    inference(resolution,[],[f82,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f82,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_xboole_0(X5,k2_xboole_0(X5,X7))
      | r1_xboole_0(X5,k2_xboole_0(X5,X6)) ) ),
    inference(resolution,[],[f79,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f63,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

% (30906)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,k2_xboole_0(X0,X1)),X0)
      | r1_xboole_0(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f62,f61])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f163,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,k2_xboole_0(X4,X5))
      | k1_xboole_0 = k1_relat_1(X4) ) ),
    inference(resolution,[],[f147,f71])).

fof(f147,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(X0,k1_xboole_0),sK4(X0,sK3(X0,k1_xboole_0))),X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f145,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f145,plain,(
    ! [X5] :
      ( r2_hidden(sK3(X5,k1_xboole_0),k1_relat_1(X5))
      | k1_xboole_0 = k1_relat_1(X5) ) ),
    inference(resolution,[],[f136,f70])).

fof(f70,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f69,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f69,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f60,f61])).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f33,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f136,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_xboole_0(X9,k2_xboole_0(X9,X10))
      | k1_relat_1(X8) = X9
      | r2_hidden(sK3(X8,X9),k1_relat_1(X8)) ) ),
    inference(resolution,[],[f89,f71])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f46,f68])).

fof(f68,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f245,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f231,f145])).

fof(f231,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,sK0)))
      | k1_xboole_0 = k7_relat_1(sK1,sK0) ) ),
    inference(resolution,[],[f214,f27])).

fof(f27,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f214,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(k1_relat_1(sK1),X1)
      | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,X1))) ) ),
    inference(superposition,[],[f63,f130])).

fof(f130,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f64,f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f289,plain,(
    r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(forward_demodulation,[],[f277,f30])).

fof(f277,plain,(
    r1_xboole_0(k5_xboole_0(k1_relat_1(sK1),k1_xboole_0),sK0) ),
    inference(superposition,[],[f215,f252])).

fof(f215,plain,(
    ! [X3] : r1_xboole_0(k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X3))),X3) ),
    inference(superposition,[],[f60,f130])).

fof(f28,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:41:30 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.53  % (30911)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.55  % (30911)Refutation found. Thanks to Tanya!
% 1.32/0.55  % SZS status Theorem for theBenchmark
% 1.32/0.55  % (30905)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.55  % (30910)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.55  % (30929)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.55  % (30933)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.55  % (30909)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.55  % (30907)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.55  % (30908)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.55  % (30934)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.55  % (30915)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.56  % (30916)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.56  % (30928)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.56  % (30920)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.56  % (30919)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.56  % (30927)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.56  % (30926)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.56  % (30927)Refutation not found, incomplete strategy% (30927)------------------------------
% 1.32/0.56  % (30927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (30925)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.52/0.56  % (30917)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.57  % (30912)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.52/0.57  % (30931)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.52/0.57  % (30913)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.57  % (30932)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.57  % (30927)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (30927)Memory used [KB]: 10746
% 1.52/0.57  % (30927)Time elapsed: 0.151 s
% 1.52/0.57  % (30927)------------------------------
% 1.52/0.57  % (30927)------------------------------
% 1.52/0.57  % (30921)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.52/0.57  % (30930)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.57  % (30918)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f305,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(subsumption_resolution,[],[f304,f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    v1_relat_1(sK1)),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f19])).
% 1.52/0.57  fof(f19,negated_conjecture,(
% 1.52/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.52/0.57    inference(negated_conjecture,[],[f18])).
% 1.52/0.57  fof(f18,conjecture,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.52/0.57  fof(f304,plain,(
% 1.52/0.57    ~v1_relat_1(sK1)),
% 1.52/0.57    inference(resolution,[],[f290,f40])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f15])).
% 1.52/0.57  fof(f15,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.52/0.57  fof(f290,plain,(
% 1.52/0.57    ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.52/0.57    inference(global_subsumption,[],[f28,f289,f287])).
% 1.52/0.57  fof(f287,plain,(
% 1.52/0.57    ~v1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.52/0.57    inference(trivial_inequality_removal,[],[f278])).
% 1.52/0.57  fof(f278,plain,(
% 1.52/0.57    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.52/0.57    inference(superposition,[],[f31,f252])).
% 1.52/0.57  fof(f252,plain,(
% 1.52/0.57    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.52/0.57    inference(subsumption_resolution,[],[f245,f164])).
% 1.52/0.57  fof(f164,plain,(
% 1.52/0.57    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k1_relat_1(X0)) )),
% 1.52/0.57    inference(resolution,[],[f163,f85])).
% 1.52/0.57  fof(f85,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X0,X1)) | k1_xboole_0 != X0) )),
% 1.52/0.57    inference(forward_demodulation,[],[f83,f61])).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X1))) = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f34,f58])).
% 1.52/0.57  fof(f58,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f35,f57])).
% 1.52/0.57  fof(f57,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f36,f56])).
% 1.52/0.57  fof(f56,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f48,f55])).
% 1.52/0.57  fof(f55,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f49,f54])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f50,f53])).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f51,f52])).
% 1.52/0.57  fof(f52,plain,(
% 1.52/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,axiom,(
% 1.52/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f11])).
% 1.52/0.57  fof(f11,axiom,(
% 1.52/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,axiom,(
% 1.52/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f7])).
% 1.52/0.57  fof(f7,axiom,(
% 1.52/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f13])).
% 1.52/0.57  fof(f13,axiom,(
% 1.52/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.52/0.57  fof(f83,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X0,X1)) | k1_xboole_0 != k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X2)))) )),
% 1.52/0.57    inference(resolution,[],[f82,f66])).
% 1.52/0.57  fof(f66,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f42,f58])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.52/0.57  fof(f82,plain,(
% 1.52/0.57    ( ! [X6,X7,X5] : (~r1_xboole_0(X5,k2_xboole_0(X5,X7)) | r1_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 1.52/0.57    inference(resolution,[],[f79,f71])).
% 1.52/0.57  fof(f71,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r1_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.52/0.57    inference(superposition,[],[f63,f61])).
% 1.52/0.57  fof(f63,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f38,f58])).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f24])).
% 1.52/0.57  % (30906)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.52/0.57    inference(ennf_transformation,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.52/0.57    inference(rectify,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.52/0.57  fof(f79,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,k2_xboole_0(X0,X1)),X0) | r1_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.52/0.57    inference(superposition,[],[f62,f61])).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f39,f58])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f24])).
% 1.52/0.57  fof(f163,plain,(
% 1.52/0.57    ( ! [X4,X5] : (~r1_xboole_0(X4,k2_xboole_0(X4,X5)) | k1_xboole_0 = k1_relat_1(X4)) )),
% 1.52/0.57    inference(resolution,[],[f147,f71])).
% 1.52/0.57  fof(f147,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0,k1_xboole_0),sK4(X0,sK3(X0,k1_xboole_0))),X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 1.52/0.57    inference(resolution,[],[f145,f67])).
% 1.52/0.57  fof(f67,plain,(
% 1.52/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f45])).
% 1.52/0.57  fof(f45,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,axiom,(
% 1.52/0.57    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.52/0.57  fof(f145,plain,(
% 1.52/0.57    ( ! [X5] : (r2_hidden(sK3(X5,k1_xboole_0),k1_relat_1(X5)) | k1_xboole_0 = k1_relat_1(X5)) )),
% 1.52/0.57    inference(resolution,[],[f136,f70])).
% 1.52/0.57  fof(f70,plain,(
% 1.52/0.57    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) )),
% 1.52/0.57    inference(superposition,[],[f69,f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.52/0.57  fof(f69,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,X0),k2_xboole_0(X0,X1))) )),
% 1.52/0.57    inference(superposition,[],[f60,f61])).
% 1.52/0.57  fof(f60,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X1)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f33,f59])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f37,f58])).
% 1.52/0.57  fof(f37,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.52/0.57  fof(f136,plain,(
% 1.52/0.57    ( ! [X10,X8,X9] : (~r1_xboole_0(X9,k2_xboole_0(X9,X10)) | k1_relat_1(X8) = X9 | r2_hidden(sK3(X8,X9),k1_relat_1(X8))) )),
% 1.52/0.57    inference(resolution,[],[f89,f71])).
% 1.52/0.57  fof(f89,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) = X1) )),
% 1.52/0.57    inference(resolution,[],[f46,f68])).
% 1.52/0.57  fof(f68,plain,(
% 1.52/0.57    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.52/0.57    inference(equality_resolution,[],[f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f14])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f14])).
% 1.52/0.57  fof(f245,plain,(
% 1.52/0.57    k1_xboole_0 = k7_relat_1(sK1,sK0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.52/0.57    inference(resolution,[],[f231,f145])).
% 1.52/0.57  fof(f231,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,sK0))) | k1_xboole_0 = k7_relat_1(sK1,sK0)) )),
% 1.52/0.57    inference(resolution,[],[f214,f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  fof(f214,plain,(
% 1.52/0.57    ( ! [X2,X1] : (~r1_xboole_0(k1_relat_1(sK1),X1) | ~r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 1.52/0.57    inference(superposition,[],[f63,f130])).
% 1.52/0.57  fof(f130,plain,(
% 1.52/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),X0))) )),
% 1.52/0.57    inference(resolution,[],[f64,f29])).
% 1.52/0.57  fof(f64,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f41,f58])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f17])).
% 1.52/0.57  fof(f17,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(flattening,[],[f22])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f16])).
% 1.52/0.57  fof(f16,axiom,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.52/0.57  fof(f289,plain,(
% 1.52/0.57    r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.52/0.57    inference(forward_demodulation,[],[f277,f30])).
% 1.52/0.57  fof(f277,plain,(
% 1.52/0.57    r1_xboole_0(k5_xboole_0(k1_relat_1(sK1),k1_xboole_0),sK0)),
% 1.52/0.57    inference(superposition,[],[f215,f252])).
% 1.52/0.57  fof(f215,plain,(
% 1.52/0.57    ( ! [X3] : (r1_xboole_0(k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X3))),X3)) )),
% 1.52/0.57    inference(superposition,[],[f60,f130])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (30911)------------------------------
% 1.52/0.57  % (30911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (30911)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (30911)Memory used [KB]: 6524
% 1.52/0.57  % (30911)Time elapsed: 0.134 s
% 1.52/0.57  % (30911)------------------------------
% 1.52/0.57  % (30911)------------------------------
% 1.52/0.57  % (30904)Success in time 0.2 s
%------------------------------------------------------------------------------
