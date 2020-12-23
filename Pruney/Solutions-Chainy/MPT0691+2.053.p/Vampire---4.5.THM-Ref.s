%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 277 expanded)
%              Number of leaves         :   21 (  74 expanded)
%              Depth                    :   21
%              Number of atoms          :  196 ( 614 expanded)
%              Number of equality atoms :   84 ( 168 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f691,plain,(
    $false ),
    inference(subsumption_resolution,[],[f690,f44])).

fof(f44,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f690,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f689,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f689,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f249,f643])).

fof(f643,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f640,f210])).

fof(f210,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f206,f130])).

fof(f130,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f128,f105])).

fof(f105,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f128,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f123,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f123,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f206,plain,(
    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f201,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f201,plain,(
    k1_relat_1(k6_relat_1(sK0)) = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f198,f170])).

fof(f170,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f169,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f169,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) ) ),
    inference(forward_demodulation,[],[f168,f106])).

fof(f106,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f58,f45])).

fof(f168,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f167,f45])).

fof(f167,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK1))) ) ),
    inference(superposition,[],[f116,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f116,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(k1_relat_1(sK1))) = X1 ) ),
    inference(resolution,[],[f59,f101])).

fof(f101,plain,(
    ! [X2] :
      ( r1_tarski(X2,k1_relat_1(sK1))
      | ~ r1_tarski(X2,sK0) ) ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

% (8862)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f198,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f196,f106])).

fof(f196,plain,(
    ! [X2,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f126,f45])).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2) ) ),
    inference(forward_demodulation,[],[f124,f47])).

fof(f124,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f51,f45])).

fof(f640,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f351,f585])).

fof(f585,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f582,f212])).

fof(f212,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(resolution,[],[f133,f42])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1) ) ),
    inference(resolution,[],[f52,f76])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f582,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f382,f210])).

fof(f382,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f85,f42])).

fof(f85,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f50,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f351,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f80,f42])).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f49,f56])).

% (8867)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f249,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X0),X1))
      | r1_tarski(X0,k10_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f74,f164])).

fof(f164,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f75,f42])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f71])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:30:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (8848)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8863)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (8864)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (8846)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (8847)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (8856)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (8843)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (8865)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (8855)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (8857)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (8842)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (8848)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (8854)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (8853)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (8869)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (8849)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (8844)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (8861)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (8868)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (8858)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (8845)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (8866)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (8860)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f691,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f690,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.55    inference(negated_conjecture,[],[f21])).
% 0.21/0.55  fof(f21,conjecture,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.55  fof(f690,plain,(
% 0.21/0.55    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f689,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.55  fof(f689,plain,(
% 0.21/0.55    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.55    inference(superposition,[],[f249,f643])).
% 0.21/0.55  fof(f643,plain,(
% 0.21/0.55    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f640,f210])).
% 0.21/0.55  fof(f210,plain,(
% 0.21/0.55    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.55    inference(superposition,[],[f206,f130])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f128,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 0.21/0.55    inference(resolution,[],[f58,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) )),
% 0.21/0.55    inference(resolution,[],[f123,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))) )),
% 0.21/0.55    inference(resolution,[],[f51,f42])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    sK0 = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.55    inference(forward_demodulation,[],[f201,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    k1_relat_1(k6_relat_1(sK0)) = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.55    inference(superposition,[],[f198,f170])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 0.21/0.55    inference(resolution,[],[f169,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK0) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f168,f106])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 0.21/0.55    inference(resolution,[],[f58,f45])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK0) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK1)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f167,f45])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(sK1)))) )),
% 0.21/0.55    inference(superposition,[],[f116,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    ( ! [X1] : (~r1_tarski(k2_relat_1(X1),sK0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(k1_relat_1(sK1))) = X1) )),
% 0.21/0.55    inference(resolution,[],[f59,f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X2] : (r1_tarski(X2,k1_relat_1(sK1)) | ~r1_tarski(X2,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f67,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  % (8862)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f196,f106])).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.55    inference(resolution,[],[f126,f45])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f124,f47])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(resolution,[],[f51,f45])).
% 0.21/0.55  fof(f640,plain,(
% 0.21/0.55    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 0.21/0.55    inference(superposition,[],[f351,f585])).
% 0.21/0.55  fof(f585,plain,(
% 0.21/0.55    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f582,f212])).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 0.21/0.55    inference(resolution,[],[f133,f42])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1)) )),
% 0.21/0.55    inference(resolution,[],[f52,f76])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.21/0.55  fof(f582,plain,(
% 0.21/0.55    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 0.21/0.55    inference(superposition,[],[f382,f210])).
% 0.21/0.55  fof(f382,plain,(
% 0.21/0.55    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.21/0.55    inference(resolution,[],[f85,f42])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))) )),
% 0.21/0.55    inference(resolution,[],[f50,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.55  fof(f351,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.21/0.55    inference(resolution,[],[f80,f42])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))) )),
% 0.21/0.55    inference(resolution,[],[f49,f56])).
% 0.21/0.55  % (8867)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.55  fof(f249,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X0),X1)) | r1_tarski(X0,k10_relat_1(sK1,X1))) )),
% 0.21/0.55    inference(superposition,[],[f74,f164])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(sK1,X1)))) )),
% 0.21/0.55    inference(resolution,[],[f75,f42])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f66,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f53,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f54,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f65,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f63,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f55,f71])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (8848)------------------------------
% 0.21/0.55  % (8848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8848)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (8848)Memory used [KB]: 11385
% 0.21/0.55  % (8848)Time elapsed: 0.124 s
% 0.21/0.55  % (8848)------------------------------
% 0.21/0.55  % (8848)------------------------------
% 0.21/0.55  % (8841)Success in time 0.191 s
%------------------------------------------------------------------------------
