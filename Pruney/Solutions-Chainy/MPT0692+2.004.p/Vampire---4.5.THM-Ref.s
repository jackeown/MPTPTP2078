%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:56 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 163 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 419 expanded)
%              Number of equality atoms :   42 ( 133 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3371,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3359,f933])).

fof(f933,plain,(
    r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f30,f892,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f892,plain,(
    r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f840,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f840,plain,(
    k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f814,f222])).

fof(f222,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f217,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f55,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f217,plain,(
    ! [X4] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X4,X4)) ),
    inference(superposition,[],[f108,f66])).

fof(f108,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f31,f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f814,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f214,f65])).

fof(f65,plain,(
    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f52])).

fof(f32,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f214,plain,(
    ! [X0] : k10_relat_1(sK1,k6_subset_1(X0,k2_relat_1(sK1))) = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f108,f90])).

fof(f90,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f3359,plain,(
    ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f538,f216])).

fof(f216,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3))
      | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3)) ) ),
    inference(superposition,[],[f108,f52])).

fof(f538,plain,(
    k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f30,f58,f210,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f210,plain,(
    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f121,f51])).

fof(f121,plain,(
    ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f33,f91,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f91,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f31,f30,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f33,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (13211)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.47  % (13220)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.47  % (13207)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.48  % (13213)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.49  % (13232)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.49  % (13205)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.49  % (13232)Refutation not found, incomplete strategy% (13232)------------------------------
% 0.21/0.49  % (13232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13220)Refutation not found, incomplete strategy% (13220)------------------------------
% 0.21/0.49  % (13220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13220)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13220)Memory used [KB]: 10618
% 0.21/0.49  % (13220)Time elapsed: 0.070 s
% 0.21/0.49  % (13220)------------------------------
% 0.21/0.49  % (13220)------------------------------
% 0.21/0.49  % (13224)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.50  % (13215)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (13232)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13232)Memory used [KB]: 10746
% 0.21/0.51  % (13232)Time elapsed: 0.093 s
% 0.21/0.51  % (13232)------------------------------
% 0.21/0.51  % (13232)------------------------------
% 0.21/0.52  % (13214)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (13214)Refutation not found, incomplete strategy% (13214)------------------------------
% 0.21/0.53  % (13214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13214)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13214)Memory used [KB]: 10746
% 0.21/0.53  % (13214)Time elapsed: 0.116 s
% 0.21/0.53  % (13214)------------------------------
% 0.21/0.53  % (13214)------------------------------
% 0.21/0.53  % (13208)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.37/0.54  % (13206)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.37/0.54  % (13233)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.54  % (13233)Refutation not found, incomplete strategy% (13233)------------------------------
% 1.37/0.54  % (13233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (13233)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (13233)Memory used [KB]: 1663
% 1.37/0.54  % (13233)Time elapsed: 0.140 s
% 1.37/0.54  % (13233)------------------------------
% 1.37/0.54  % (13233)------------------------------
% 1.37/0.54  % (13226)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.37/0.54  % (13231)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.54  % (13225)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.54  % (13204)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.37/0.55  % (13218)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.49/0.55  % (13216)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.55  % (13216)Refutation not found, incomplete strategy% (13216)------------------------------
% 1.49/0.55  % (13216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (13216)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (13216)Memory used [KB]: 10746
% 1.49/0.55  % (13216)Time elapsed: 0.151 s
% 1.49/0.55  % (13216)------------------------------
% 1.49/0.55  % (13216)------------------------------
% 1.49/0.56  % (13219)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.49/0.56  % (13223)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.49/0.56  % (13228)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.49/0.56  % (13229)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.49/0.56  % (13227)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.49/0.56  % (13222)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.49/0.57  % (13230)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.49/0.57  % (13210)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.58  % (13212)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.49/0.58  % (13221)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.58  % (13209)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.49/0.58  % (13217)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.49/0.59  % (13207)Refutation not found, incomplete strategy% (13207)------------------------------
% 1.49/0.59  % (13207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (13207)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (13207)Memory used [KB]: 6140
% 1.49/0.59  % (13207)Time elapsed: 0.196 s
% 1.49/0.59  % (13207)------------------------------
% 1.49/0.59  % (13207)------------------------------
% 2.00/0.63  % (13235)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.00/0.64  % (13236)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.00/0.66  % (13237)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.00/0.66  % (13237)Refutation not found, incomplete strategy% (13237)------------------------------
% 2.00/0.66  % (13237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.66  % (13237)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.66  
% 2.00/0.66  % (13237)Memory used [KB]: 6140
% 2.00/0.66  % (13237)Time elapsed: 0.110 s
% 2.00/0.66  % (13237)------------------------------
% 2.00/0.66  % (13237)------------------------------
% 2.38/0.68  % (13239)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.38/0.70  % (13238)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.38/0.71  % (13240)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.38/0.74  % (13223)Refutation found. Thanks to Tanya!
% 2.38/0.74  % SZS status Theorem for theBenchmark
% 2.38/0.74  % SZS output start Proof for theBenchmark
% 2.38/0.74  fof(f3371,plain,(
% 2.38/0.74    $false),
% 2.38/0.74    inference(subsumption_resolution,[],[f3359,f933])).
% 2.38/0.74  fof(f933,plain,(
% 2.38/0.74    r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),
% 2.38/0.74    inference(unit_resulting_resolution,[],[f30,f892,f38])).
% 2.38/0.74  fof(f38,plain,(
% 2.38/0.74    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 2.38/0.74    inference(cnf_transformation,[],[f23])).
% 2.38/0.74  fof(f23,plain,(
% 2.38/0.74    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.38/0.74    inference(flattening,[],[f22])).
% 2.38/0.74  fof(f22,plain,(
% 2.38/0.74    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.38/0.74    inference(ennf_transformation,[],[f15])).
% 2.38/0.74  fof(f15,axiom,(
% 2.38/0.74    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.38/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.38/0.74  fof(f892,plain,(
% 2.38/0.74    r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))),
% 2.38/0.74    inference(unit_resulting_resolution,[],[f840,f51])).
% 2.38/0.74  fof(f51,plain,(
% 2.38/0.74    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 2.38/0.74    inference(definition_unfolding,[],[f44,f46])).
% 2.38/0.74  fof(f46,plain,(
% 2.38/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.38/0.74    inference(cnf_transformation,[],[f9])).
% 2.38/0.74  fof(f9,axiom,(
% 2.38/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.38/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.38/0.74  fof(f44,plain,(
% 2.38/0.74    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.38/0.74    inference(cnf_transformation,[],[f3])).
% 2.38/0.74  fof(f3,axiom,(
% 2.38/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.38/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.38/0.74  fof(f840,plain,(
% 2.38/0.74    k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,sK0),k1_relat_1(sK1))),
% 2.38/0.74    inference(forward_demodulation,[],[f814,f222])).
% 2.38/0.74  fof(f222,plain,(
% 2.38/0.74    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 2.38/0.74    inference(forward_demodulation,[],[f217,f66])).
% 2.38/0.74  fof(f66,plain,(
% 2.38/0.74    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 2.38/0.74    inference(unit_resulting_resolution,[],[f55,f52])).
% 2.38/0.74  fof(f52,plain,(
% 2.38/0.74    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.38/0.74    inference(definition_unfolding,[],[f43,f46])).
% 2.38/0.74  fof(f43,plain,(
% 2.38/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.38/0.74    inference(cnf_transformation,[],[f3])).
% 2.38/0.74  fof(f55,plain,(
% 2.38/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.38/0.74    inference(equality_resolution,[],[f35])).
% 2.38/0.74  fof(f35,plain,(
% 2.38/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.38/0.74    inference(cnf_transformation,[],[f2])).
% 2.38/0.74  fof(f2,axiom,(
% 2.38/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.38/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.38/0.74  fof(f217,plain,(
% 2.38/0.74    ( ! [X4] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X4,X4))) )),
% 2.38/0.74    inference(superposition,[],[f108,f66])).
% 2.38/0.74  fof(f108,plain,(
% 2.38/0.74    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 2.38/0.74    inference(unit_resulting_resolution,[],[f31,f30,f39])).
% 2.38/0.74  fof(f39,plain,(
% 2.38/0.74    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 2.38/0.74    inference(cnf_transformation,[],[f25])).
% 2.38/0.74  fof(f25,plain,(
% 2.38/0.74    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.38/0.74    inference(flattening,[],[f24])).
% 2.38/0.74  fof(f24,plain,(
% 2.38/0.74    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.38/0.74    inference(ennf_transformation,[],[f13])).
% 2.38/0.74  fof(f13,axiom,(
% 2.38/0.74    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.38/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 2.38/0.74  fof(f31,plain,(
% 2.38/0.74    v1_funct_1(sK1)),
% 2.38/0.74    inference(cnf_transformation,[],[f19])).
% 2.38/0.74  fof(f19,plain,(
% 2.38/0.74    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.38/0.74    inference(flattening,[],[f18])).
% 2.38/0.74  fof(f18,plain,(
% 2.38/0.74    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.38/0.74    inference(ennf_transformation,[],[f17])).
% 2.38/0.74  fof(f17,negated_conjecture,(
% 2.38/0.74    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.38/0.74    inference(negated_conjecture,[],[f16])).
% 2.38/0.74  fof(f16,conjecture,(
% 2.38/0.74    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.38/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 2.38/0.74  fof(f814,plain,(
% 2.38/0.74    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,sK0),k1_relat_1(sK1))),
% 2.38/0.74    inference(superposition,[],[f214,f65])).
% 2.38/0.74  fof(f65,plain,(
% 2.38/0.74    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1))),
% 2.38/0.74    inference(unit_resulting_resolution,[],[f32,f52])).
% 2.38/0.74  fof(f32,plain,(
% 2.38/0.74    r1_tarski(sK0,k2_relat_1(sK1))),
% 2.38/0.74    inference(cnf_transformation,[],[f19])).
% 2.38/0.74  fof(f214,plain,(
% 2.38/0.74    ( ! [X0] : (k10_relat_1(sK1,k6_subset_1(X0,k2_relat_1(sK1))) = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.38/0.74    inference(superposition,[],[f108,f90])).
% 2.38/0.74  fof(f90,plain,(
% 2.38/0.74    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 2.38/0.74    inference(unit_resulting_resolution,[],[f30,f41])).
% 2.38/0.74  fof(f41,plain,(
% 2.38/0.74    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.38/0.74    inference(cnf_transformation,[],[f28])).
% 2.38/0.74  fof(f28,plain,(
% 2.38/0.74    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.38/0.74    inference(ennf_transformation,[],[f11])).
% 2.38/0.74  fof(f11,axiom,(
% 2.38/0.74    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.38/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.38/0.74  fof(f30,plain,(
% 2.38/0.74    v1_relat_1(sK1)),
% 2.38/0.74    inference(cnf_transformation,[],[f19])).
% 2.38/0.74  fof(f3359,plain,(
% 2.38/0.74    ~r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),
% 2.38/0.74    inference(unit_resulting_resolution,[],[f538,f216])).
% 2.38/0.74  fof(f216,plain,(
% 2.38/0.74    ( ! [X2,X3] : (~r1_tarski(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3)) | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X3))) )),
% 2.38/0.74    inference(superposition,[],[f108,f52])).
% 2.38/0.74  fof(f538,plain,(
% 2.38/0.74    k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),
% 2.38/0.74    inference(unit_resulting_resolution,[],[f30,f58,f210,f40])).
% 2.38/0.74  fof(f40,plain,(
% 2.38/0.74    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.38/0.74    inference(cnf_transformation,[],[f27])).
% 2.38/0.74  fof(f27,plain,(
% 2.38/0.74    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 2.38/0.74    inference(flattening,[],[f26])).
% 2.38/0.74  fof(f26,plain,(
% 2.38/0.74    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 2.38/0.74    inference(ennf_transformation,[],[f12])).
% 2.38/0.74  fof(f12,axiom,(
% 2.38/0.74    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 2.38/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 2.38/0.75  fof(f210,plain,(
% 2.38/0.75    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 2.38/0.75    inference(unit_resulting_resolution,[],[f121,f51])).
% 2.38/0.75  fof(f121,plain,(
% 2.38/0.75    ~r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 2.38/0.75    inference(unit_resulting_resolution,[],[f33,f91,f36])).
% 2.38/0.75  fof(f36,plain,(
% 2.38/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.38/0.75    inference(cnf_transformation,[],[f2])).
% 2.38/0.75  fof(f91,plain,(
% 2.38/0.75    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 2.38/0.75    inference(unit_resulting_resolution,[],[f31,f30,f37])).
% 2.38/0.75  fof(f37,plain,(
% 2.38/0.75    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 2.38/0.75    inference(cnf_transformation,[],[f21])).
% 2.38/0.75  fof(f21,plain,(
% 2.38/0.75    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.38/0.75    inference(flattening,[],[f20])).
% 2.38/0.75  fof(f20,plain,(
% 2.38/0.75    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.38/0.75    inference(ennf_transformation,[],[f14])).
% 2.38/0.75  fof(f14,axiom,(
% 2.38/0.75    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.38/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 2.38/0.75  fof(f33,plain,(
% 2.38/0.75    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 2.38/0.75    inference(cnf_transformation,[],[f19])).
% 2.38/0.75  fof(f58,plain,(
% 2.38/0.75    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK1))) )),
% 2.38/0.75    inference(unit_resulting_resolution,[],[f32,f50])).
% 2.38/0.75  fof(f50,plain,(
% 2.38/0.75    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.38/0.75    inference(definition_unfolding,[],[f42,f46])).
% 2.38/0.75  fof(f42,plain,(
% 2.38/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1)) )),
% 2.38/0.75    inference(cnf_transformation,[],[f29])).
% 2.38/0.75  fof(f29,plain,(
% 2.38/0.75    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.38/0.75    inference(ennf_transformation,[],[f4])).
% 2.38/0.75  fof(f4,axiom,(
% 2.38/0.75    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 2.38/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 2.38/0.75  % SZS output end Proof for theBenchmark
% 2.38/0.75  % (13223)------------------------------
% 2.38/0.75  % (13223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.75  % (13223)Termination reason: Refutation
% 2.38/0.75  
% 2.38/0.75  % (13223)Memory used [KB]: 3070
% 2.38/0.75  % (13223)Time elapsed: 0.344 s
% 2.38/0.75  % (13223)------------------------------
% 2.38/0.75  % (13223)------------------------------
% 2.85/0.75  % (13203)Success in time 0.383 s
%------------------------------------------------------------------------------
