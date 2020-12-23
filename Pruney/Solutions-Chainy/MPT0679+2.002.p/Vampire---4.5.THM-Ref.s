%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 241 expanded)
%              Number of leaves         :   13 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 ( 451 expanded)
%              Number of equality atoms :   35 ( 171 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(subsumption_resolution,[],[f408,f68])).

fof(f68,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f50,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f34,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

% (831)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f408,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f407,f53])).

fof(f53,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f24,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( v2_funct_1(X2)
         => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f407,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f406,f104])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f59,f97])).

fof(f97,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f50,f77,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f77,plain,(
    ! [X0] : r1_tarski(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f51,f39,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k6_subset_1(X1,X2)) ) ),
    inference(definition_unfolding,[],[f40,f35])).

% (824)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f406,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(sK0,sK1))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f405,f192])).

fof(f192,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(k6_subset_1(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f50,f80,f32])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),X1)) ),
    inference(unit_resulting_resolution,[],[f51,f49,f48])).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f41,f35])).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

% (838)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f405,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(k6_subset_1(sK0,sK1),sK1))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f402,f110])).

fof(f110,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(sK2,X0),k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(unit_resulting_resolution,[],[f26,f24,f25,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(X2,X0),k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f38,f43,f43])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f402,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f68,f358,f63])).

% (811)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_tarski(k6_subset_1(X0,k6_subset_1(X0,X1)),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k6_subset_1(X0,k6_subset_1(X0,X1))) ) ),
    inference(extensionality_resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,k6_subset_1(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f358,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f270,f125,f48])).

fof(f125,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f27,f92,f32])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f24,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

fof(f27,plain,(
    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f270,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X0)) ),
    inference(superposition,[],[f232,f46])).

fof(f46,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f35,f35,f43])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f232,plain,(
    ! [X12,X13] : r1_tarski(k9_relat_1(sK2,k6_subset_1(X12,k6_subset_1(X12,X13))),k9_relat_1(sK2,X12)) ),
    inference(superposition,[],[f50,f110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (836)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (827)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (814)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (832)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (837)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (812)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (823)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (832)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (829)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (815)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (842)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (818)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (817)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f409,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f408,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 0.21/0.54    inference(superposition,[],[f50,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f39,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f34,f35,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  % (831)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f42,f35])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.54  fof(f408,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f407,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f24,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1)) & v2_funct_1(X2) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1)) & v2_funct_1(X2)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f14])).
% 0.21/0.54  fof(f14,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 0.21/0.54  fof(f407,plain,(
% 0.21/0.54    ~r1_tarski(k9_relat_1(sK2,k1_xboole_0),k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f406,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f59,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f50,f77,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f51,f39,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k6_subset_1(X1,X2))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f40,f35])).
% 0.21/0.54  % (824)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f406,plain,(
% 0.21/0.54    ~r1_tarski(k9_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(sK0,sK1))),k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f405,f192])).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(k6_subset_1(X0,X1),X1)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f50,f80,f32])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),X1))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f51,f49,f48])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f41,f35])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.54  % (838)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  fof(f405,plain,(
% 0.21/0.54    ~r1_tarski(k9_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(k6_subset_1(sK0,sK1),sK1))),k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f402,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(sK2,X0),k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f26,f24,f25,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k9_relat_1(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(X2,X0),k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f43,f43])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    v2_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f402,plain,(
% 0.21/0.54    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))),k1_xboole_0)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f68,f358,f63])).
% 0.21/0.54  % (811)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_tarski(k6_subset_1(X0,k6_subset_1(X0,X1)),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 0.21/0.54    inference(extensionality_resolution,[],[f32,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,k6_subset_1(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f28,f43])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f270,f125,f48])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f27,f92,f32])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f24,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X0))) )),
% 0.21/0.54    inference(superposition,[],[f232,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f33,f35,f35,f43])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    ( ! [X12,X13] : (r1_tarski(k9_relat_1(sK2,k6_subset_1(X12,k6_subset_1(X12,X13))),k9_relat_1(sK2,X12))) )),
% 0.21/0.54    inference(superposition,[],[f50,f110])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (832)------------------------------
% 0.21/0.54  % (832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (832)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (832)Memory used [KB]: 1918
% 0.21/0.54  % (832)Time elapsed: 0.137 s
% 0.21/0.54  % (832)------------------------------
% 0.21/0.54  % (832)------------------------------
% 0.21/0.55  % (809)Success in time 0.186 s
%------------------------------------------------------------------------------
