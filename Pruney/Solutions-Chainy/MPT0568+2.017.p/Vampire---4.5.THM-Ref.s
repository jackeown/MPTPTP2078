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
% DateTime   : Thu Dec  3 12:50:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 133 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  124 ( 234 expanded)
%              Number of equality atoms :   42 (  82 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f22,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f80,f68])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k10_relat_1(k1_xboole_0,X0)),k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f67,f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
      | r2_hidden(X0,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))) ) ),
    inference(subsumption_resolution,[],[f66,f23])).

fof(f23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
      | r2_hidden(X0,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f64,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f64,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X2,k10_relat_1(k1_xboole_0,X3))
      | r2_hidden(X2,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
      | ~ r2_hidden(X2,k10_relat_1(k1_xboole_0,X3))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X2,k10_relat_1(k1_xboole_0,X3)) ) ),
    inference(resolution,[],[f61,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X2,k1_xboole_0),X1)
      | r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
      | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X2)) ) ),
    inference(subsumption_resolution,[],[f60,f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
      | ~ r2_hidden(sK2(X0,X2,k1_xboole_0),X1)
      | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X2))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f59,f26])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(X0,k10_relat_1(k1_xboole_0,X2))
      | ~ r2_hidden(sK2(X0,X1,k1_xboole_0),X2)
      | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ) ),
    inference(subsumption_resolution,[],[f58,f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,k1_xboole_0),X2)
      | r2_hidden(X0,k10_relat_1(k1_xboole_0,X2))
      | ~ r2_hidden(sK2(X0,X1,k1_xboole_0),k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,k10_relat_1(k1_xboole_0,X2))
      | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f56,f23])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(k4_tarski(X2,X0),X1)
      | ~ r2_hidden(X0,X3)
      | r2_hidden(X2,k10_relat_1(X1,X3))
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(resolution,[],[f35,f26])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ),
    inference(subsumption_resolution,[],[f79,f23])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f77,f26])).

fof(f77,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X2,k10_relat_1(k1_xboole_0,X3)) ) ),
    inference(resolution,[],[f74,f33])).

fof(f74,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f55,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f24,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f55,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f37,f49,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f47])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f22,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (23076)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (23068)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (23076)Refutation not found, incomplete strategy% (23076)------------------------------
% 0.22/0.51  % (23076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23060)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (23076)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  % (23079)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  
% 0.22/0.51  % (23076)Memory used [KB]: 10618
% 0.22/0.51  % (23076)Time elapsed: 0.056 s
% 0.22/0.51  % (23076)------------------------------
% 0.22/0.51  % (23076)------------------------------
% 0.22/0.51  % (23058)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (23058)Refutation not found, incomplete strategy% (23058)------------------------------
% 0.22/0.51  % (23058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23058)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23058)Memory used [KB]: 6140
% 0.22/0.51  % (23058)Time elapsed: 0.097 s
% 0.22/0.51  % (23058)------------------------------
% 0.22/0.51  % (23058)------------------------------
% 0.22/0.51  % (23065)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (23065)Refutation not found, incomplete strategy% (23065)------------------------------
% 0.22/0.51  % (23065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23065)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23065)Memory used [KB]: 10618
% 0.22/0.51  % (23065)Time elapsed: 0.106 s
% 0.22/0.51  % (23065)------------------------------
% 0.22/0.51  % (23065)------------------------------
% 0.22/0.51  % (23060)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0),
% 0.22/0.51    inference(superposition,[],[f22,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(resolution,[],[f80,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK1(k10_relat_1(k1_xboole_0,X0)),k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(resolution,[],[f67,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | r2_hidden(X0,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f66,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | r2_hidden(X0,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.22/0.51    inference(resolution,[],[f64,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X2,k10_relat_1(k1_xboole_0,X3)) | r2_hidden(X2,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X3] : (r2_hidden(X2,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))) | ~r2_hidden(X2,k10_relat_1(k1_xboole_0,X3)) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(X2,k10_relat_1(k1_xboole_0,X3))) )),
% 0.22/0.51    inference(resolution,[],[f61,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X2,k1_xboole_0),X1) | r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X2))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f60,f23])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | ~r2_hidden(sK2(X0,X2,k1_xboole_0),X1) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X2)) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.22/0.51    inference(resolution,[],[f59,f26])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(k1_xboole_0) | r2_hidden(X0,k10_relat_1(k1_xboole_0,X2)) | ~r2_hidden(sK2(X0,X1,k1_xboole_0),X2) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f58,f32])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,k1_xboole_0),X2) | r2_hidden(X0,k10_relat_1(k1_xboole_0,X2)) | ~r2_hidden(sK2(X0,X1,k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) )),
% 0.22/0.51    inference(resolution,[],[f57,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,X2) | r2_hidden(X0,k10_relat_1(k1_xboole_0,X2)) | ~r2_hidden(X1,k2_relat_1(k1_xboole_0))) )),
% 0.22/0.51    inference(resolution,[],[f56,f23])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X1) | ~r2_hidden(k4_tarski(X2,X0),X1) | ~r2_hidden(X0,X3) | r2_hidden(X2,k10_relat_1(X1,X3)) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 0.22/0.51    inference(resolution,[],[f35,f26])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f79,f23])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.22/0.51    inference(resolution,[],[f77,f26])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X2,k10_relat_1(k1_xboole_0,X3))) )),
% 0.22/0.51    inference(resolution,[],[f74,f33])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(superposition,[],[f55,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f24,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f30,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f28,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f29,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f31,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f39,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f40,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f41,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) )),
% 0.22/0.52    inference(equality_resolution,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f37,f49,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f25,f47])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,negated_conjecture,(
% 0.22/0.52    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.52    inference(negated_conjecture,[],[f16])).
% 0.22/0.52  fof(f16,conjecture,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (23060)------------------------------
% 0.22/0.52  % (23060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23060)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (23060)Memory used [KB]: 6268
% 0.22/0.52  % (23060)Time elapsed: 0.063 s
% 0.22/0.52  % (23060)------------------------------
% 0.22/0.52  % (23060)------------------------------
% 0.22/0.52  % (23071)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (23055)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (23051)Success in time 0.156 s
%------------------------------------------------------------------------------
