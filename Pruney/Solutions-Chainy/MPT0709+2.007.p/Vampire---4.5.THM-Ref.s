%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:36 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 132 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  164 ( 493 expanded)
%              Number of equality atoms :   38 ( 110 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(resolution,[],[f198,f156])).

fof(f156,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(subsumption_resolution,[],[f155,f65])).

fof(f65,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f155,plain,
    ( sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f136,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f136,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f134,f61])).

fof(f61,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f134,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f63,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f63,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f198,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f197,f61])).

fof(f197,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f196,f62])).

fof(f62,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f196,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f195,f122])).

fof(f122,plain,(
    ! [X1] : r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f195,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f190,f64])).

fof(f64,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f190,plain,(
    ! [X0] :
      ( ~ v2_funct_1(sK1)
      | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f182,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f182,plain,(
    ! [X7] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X7)),X7) ),
    inference(superposition,[],[f103,f159])).

fof(f159,plain,(
    ! [X1] : k6_subset_1(X1,k6_subset_1(X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1)) ),
    inference(superposition,[],[f128,f105])).

fof(f105,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f81,f101,f78,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f101,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f80,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f128,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f127,f123])).

fof(f123,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f61,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f127,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f124,f61])).

fof(f124,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK1,k1_relat_1(sK1))))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f62,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f85,f101])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f76,f78])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:51:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (17340)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (17332)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (17323)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (17324)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (17331)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (17339)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (17339)Refutation not found, incomplete strategy% (17339)------------------------------
% 0.22/0.58  % (17339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (17339)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (17339)Memory used [KB]: 10746
% 0.22/0.58  % (17339)Time elapsed: 0.130 s
% 0.22/0.58  % (17339)------------------------------
% 0.22/0.58  % (17339)------------------------------
% 1.60/0.60  % (17317)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.60/0.60  % (17320)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.60/0.61  % (17341)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.60/0.61  % (17338)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.60/0.61  % (17335)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.60/0.61  % (17325)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.60/0.61  % (17330)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.60/0.61  % (17327)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.60/0.61  % (17336)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.60/0.61  % (17342)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.90/0.62  % (17322)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.90/0.62  % (17333)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.90/0.62  % (17344)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.90/0.62  % (17343)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.90/0.62  % (17321)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.90/0.62  % (17318)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.90/0.62  % (17319)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.90/0.63  % (17328)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.90/0.63  % (17345)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.90/0.63  % (17326)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.90/0.63  % (17334)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.90/0.64  % (17334)Refutation not found, incomplete strategy% (17334)------------------------------
% 1.90/0.64  % (17334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.64  % (17334)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.64  
% 1.90/0.64  % (17334)Memory used [KB]: 10618
% 1.90/0.64  % (17334)Time elapsed: 0.151 s
% 1.90/0.64  % (17334)------------------------------
% 1.90/0.64  % (17334)------------------------------
% 1.90/0.64  % (17327)Refutation not found, incomplete strategy% (17327)------------------------------
% 1.90/0.64  % (17327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.64  % (17327)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.64  
% 1.90/0.64  % (17327)Memory used [KB]: 10746
% 1.90/0.64  % (17327)Time elapsed: 0.180 s
% 1.90/0.64  % (17327)------------------------------
% 1.90/0.64  % (17327)------------------------------
% 1.90/0.64  % (17325)Refutation found. Thanks to Tanya!
% 1.90/0.64  % SZS status Theorem for theBenchmark
% 1.90/0.64  % SZS output start Proof for theBenchmark
% 1.90/0.64  fof(f295,plain,(
% 1.90/0.64    $false),
% 1.90/0.64    inference(resolution,[],[f198,f156])).
% 1.90/0.64  fof(f156,plain,(
% 1.90/0.64    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.90/0.64    inference(subsumption_resolution,[],[f155,f65])).
% 1.90/0.64  fof(f65,plain,(
% 1.90/0.64    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.90/0.64    inference(cnf_transformation,[],[f44])).
% 1.90/0.64  fof(f44,plain,(
% 1.90/0.64    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.90/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43])).
% 1.90/0.64  fof(f43,plain,(
% 1.90/0.64    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.90/0.64    introduced(choice_axiom,[])).
% 1.90/0.64  fof(f25,plain,(
% 1.90/0.64    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.90/0.64    inference(flattening,[],[f24])).
% 1.90/0.64  fof(f24,plain,(
% 1.90/0.64    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.90/0.64    inference(ennf_transformation,[],[f23])).
% 1.90/0.64  fof(f23,negated_conjecture,(
% 1.90/0.64    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.90/0.64    inference(negated_conjecture,[],[f22])).
% 1.90/0.64  fof(f22,conjecture,(
% 1.90/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 1.90/0.64  fof(f155,plain,(
% 1.90/0.64    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.90/0.64    inference(resolution,[],[f136,f89])).
% 1.90/0.64  fof(f89,plain,(
% 1.90/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.90/0.64    inference(cnf_transformation,[],[f51])).
% 1.90/0.64  fof(f51,plain,(
% 1.90/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.90/0.64    inference(flattening,[],[f50])).
% 1.90/0.64  fof(f50,plain,(
% 1.90/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.90/0.64    inference(nnf_transformation,[],[f4])).
% 1.90/0.64  fof(f4,axiom,(
% 1.90/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.90/0.64  fof(f136,plain,(
% 1.90/0.64    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.90/0.64    inference(subsumption_resolution,[],[f134,f61])).
% 1.90/0.64  fof(f61,plain,(
% 1.90/0.64    v1_relat_1(sK1)),
% 1.90/0.64    inference(cnf_transformation,[],[f44])).
% 1.90/0.64  fof(f134,plain,(
% 1.90/0.64    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 1.90/0.64    inference(resolution,[],[f63,f84])).
% 1.90/0.64  fof(f84,plain,(
% 1.90/0.64    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 1.90/0.64    inference(cnf_transformation,[],[f33])).
% 1.90/0.64  fof(f33,plain,(
% 1.90/0.64    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.90/0.64    inference(flattening,[],[f32])).
% 1.90/0.64  fof(f32,plain,(
% 1.90/0.64    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.90/0.64    inference(ennf_transformation,[],[f18])).
% 1.90/0.64  fof(f18,axiom,(
% 1.90/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.90/0.64  fof(f63,plain,(
% 1.90/0.64    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.90/0.64    inference(cnf_transformation,[],[f44])).
% 1.90/0.64  fof(f198,plain,(
% 1.90/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.90/0.64    inference(subsumption_resolution,[],[f197,f61])).
% 1.90/0.64  fof(f197,plain,(
% 1.90/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) )),
% 1.90/0.64    inference(subsumption_resolution,[],[f196,f62])).
% 1.90/0.64  fof(f62,plain,(
% 1.90/0.64    v1_funct_1(sK1)),
% 1.90/0.64    inference(cnf_transformation,[],[f44])).
% 1.90/0.64  fof(f196,plain,(
% 1.90/0.64    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.90/0.64    inference(subsumption_resolution,[],[f195,f122])).
% 1.90/0.64  fof(f122,plain,(
% 1.90/0.64    ( ! [X1] : (r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1))) )),
% 1.90/0.64    inference(resolution,[],[f61,f82])).
% 1.90/0.64  fof(f82,plain,(
% 1.90/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 1.90/0.64    inference(cnf_transformation,[],[f30])).
% 1.90/0.64  fof(f30,plain,(
% 1.90/0.64    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.90/0.64    inference(ennf_transformation,[],[f14])).
% 1.90/0.64  fof(f14,axiom,(
% 1.90/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.90/0.64  fof(f195,plain,(
% 1.90/0.64    ( ! [X0] : (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.90/0.64    inference(subsumption_resolution,[],[f190,f64])).
% 1.90/0.64  fof(f64,plain,(
% 1.90/0.64    v2_funct_1(sK1)),
% 1.90/0.64    inference(cnf_transformation,[],[f44])).
% 1.90/0.64  fof(f190,plain,(
% 1.90/0.64    ( ! [X0] : (~v2_funct_1(sK1) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.90/0.64    inference(resolution,[],[f182,f94])).
% 1.90/0.64  fof(f94,plain,(
% 1.90/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.90/0.64    inference(cnf_transformation,[],[f42])).
% 1.90/0.64  fof(f42,plain,(
% 1.90/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.90/0.64    inference(flattening,[],[f41])).
% 1.90/0.64  fof(f41,plain,(
% 1.90/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.90/0.64    inference(ennf_transformation,[],[f21])).
% 1.90/0.64  fof(f21,axiom,(
% 1.90/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 1.90/0.64  fof(f182,plain,(
% 1.90/0.64    ( ! [X7] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X7)),X7)) )),
% 1.90/0.64    inference(superposition,[],[f103,f159])).
% 1.90/0.64  fof(f159,plain,(
% 1.90/0.64    ( ! [X1] : (k6_subset_1(X1,k6_subset_1(X1,k2_relat_1(sK1))) = k9_relat_1(sK1,k10_relat_1(sK1,X1))) )),
% 1.90/0.64    inference(superposition,[],[f128,f105])).
% 1.90/0.64  fof(f105,plain,(
% 1.90/0.64    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.90/0.64    inference(definition_unfolding,[],[f81,f101,f78,f78])).
% 1.90/0.64  fof(f78,plain,(
% 1.90/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.90/0.64    inference(cnf_transformation,[],[f11])).
% 1.90/0.64  fof(f11,axiom,(
% 1.90/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.90/0.64  fof(f101,plain,(
% 1.90/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.90/0.64    inference(definition_unfolding,[],[f79,f80])).
% 1.90/0.64  fof(f80,plain,(
% 1.90/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.90/0.64    inference(cnf_transformation,[],[f10])).
% 1.90/0.64  fof(f10,axiom,(
% 1.90/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.90/0.64  fof(f79,plain,(
% 1.90/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.90/0.64    inference(cnf_transformation,[],[f12])).
% 1.90/0.64  fof(f12,axiom,(
% 1.90/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.90/0.64  fof(f81,plain,(
% 1.90/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.90/0.64    inference(cnf_transformation,[],[f9])).
% 1.90/0.64  fof(f9,axiom,(
% 1.90/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.90/0.64  fof(f128,plain,(
% 1.90/0.64    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK1)))) )),
% 1.90/0.64    inference(forward_demodulation,[],[f127,f123])).
% 1.90/0.64  fof(f123,plain,(
% 1.90/0.64    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.90/0.64    inference(resolution,[],[f61,f68])).
% 1.90/0.64  fof(f68,plain,(
% 1.90/0.64    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.90/0.64    inference(cnf_transformation,[],[f26])).
% 1.90/0.64  fof(f26,plain,(
% 1.90/0.64    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.90/0.64    inference(ennf_transformation,[],[f13])).
% 1.90/0.64  fof(f13,axiom,(
% 1.90/0.64    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.90/0.64  fof(f127,plain,(
% 1.90/0.64    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK1,k1_relat_1(sK1))))) )),
% 1.90/0.64    inference(subsumption_resolution,[],[f124,f61])).
% 1.90/0.64  fof(f124,plain,(
% 1.90/0.64    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK1,k1_relat_1(sK1)))) | ~v1_relat_1(sK1)) )),
% 1.90/0.64    inference(resolution,[],[f62,f106])).
% 1.90/0.64  fof(f106,plain,(
% 1.90/0.64    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 1.90/0.64    inference(definition_unfolding,[],[f85,f101])).
% 1.90/0.64  fof(f85,plain,(
% 1.90/0.64    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.90/0.64    inference(cnf_transformation,[],[f35])).
% 1.90/0.64  fof(f35,plain,(
% 1.90/0.64    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.90/0.64    inference(flattening,[],[f34])).
% 1.90/0.64  fof(f34,plain,(
% 1.90/0.64    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.90/0.64    inference(ennf_transformation,[],[f20])).
% 1.90/0.64  fof(f20,axiom,(
% 1.90/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 1.90/0.64  fof(f103,plain,(
% 1.90/0.64    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.90/0.64    inference(definition_unfolding,[],[f76,f78])).
% 1.90/0.64  fof(f76,plain,(
% 1.90/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.90/0.64    inference(cnf_transformation,[],[f6])).
% 1.90/0.64  fof(f6,axiom,(
% 1.90/0.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.90/0.64  % SZS output end Proof for theBenchmark
% 1.90/0.64  % (17325)------------------------------
% 1.90/0.64  % (17325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.64  % (17325)Termination reason: Refutation
% 1.90/0.64  
% 1.90/0.64  % (17325)Memory used [KB]: 10874
% 1.90/0.64  % (17325)Time elapsed: 0.188 s
% 1.90/0.64  % (17325)------------------------------
% 1.90/0.64  % (17325)------------------------------
% 1.90/0.64  % (17329)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.90/0.65  % (17316)Success in time 0.274 s
%------------------------------------------------------------------------------
