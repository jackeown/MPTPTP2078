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
% DateTime   : Thu Dec  3 12:54:15 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 170 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  185 ( 615 expanded)
%              Number of equality atoms :   44 (  89 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12152)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f531,plain,(
    $false ),
    inference(subsumption_resolution,[],[f526,f37])).

fof(f37,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f526,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f516,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f95,f88])).

fof(f88,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f55,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f38,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

% (12138)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k6_subset_1(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(extensionality_resolution,[],[f46,f55])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (12145)Refutation not found, incomplete strategy% (12145)------------------------------
% (12145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12145)Termination reason: Refutation not found, incomplete strategy

% (12145)Memory used [KB]: 10746
% (12145)Time elapsed: 0.166 s
% (12145)------------------------------
% (12145)------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

% (12144)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f516,plain,(
    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f515,f461])).

fof(f461,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f453,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(resolution,[],[f54,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f453,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f180,f75])).

fof(f180,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f179,f32])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f179,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f515,plain,(
    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f514,f32])).

fof(f514,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f512,f238])).

fof(f238,plain,(
    ! [X8] : r1_tarski(k6_subset_1(sK0,X8),k1_relat_1(sK2)) ),
    inference(superposition,[],[f176,f66])).

fof(f66,plain,(
    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f176,plain,(
    ! [X6,X7,X5] : r1_tarski(k6_subset_1(X5,X6),k2_xboole_0(X5,X7)) ),
    inference(superposition,[],[f68,f64])).

fof(f64,plain,(
    ! [X4,X3] : k2_xboole_0(k6_subset_1(X3,X4),X3) = X3 ),
    inference(resolution,[],[f43,f53])).

fof(f68,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f50,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f512,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f42,f491])).

fof(f491,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f211,f78])).

fof(f78,plain,(
    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f54,f34])).

fof(f34,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f211,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f210,f32])).

fof(f210,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f209,f33])).

fof(f209,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:57:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.53  % (12147)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.54  % (12139)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (12150)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.55  % (12155)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.55  % (12135)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.56  % (12137)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.57  % (12157)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.58  % (12161)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.58  % (12161)Refutation not found, incomplete strategy% (12161)------------------------------
% 0.19/0.58  % (12161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (12161)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.58  
% 0.19/0.58  % (12161)Memory used [KB]: 10746
% 0.19/0.58  % (12161)Time elapsed: 0.173 s
% 0.19/0.58  % (12161)------------------------------
% 0.19/0.58  % (12161)------------------------------
% 0.19/0.58  % (12158)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.66/0.58  % (12153)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.66/0.58  % (12145)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.66/0.58  % (12139)Refutation found. Thanks to Tanya!
% 1.66/0.58  % SZS status Theorem for theBenchmark
% 1.66/0.58  % SZS output start Proof for theBenchmark
% 1.66/0.58  % (12152)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.58  fof(f531,plain,(
% 1.66/0.58    $false),
% 1.66/0.58    inference(subsumption_resolution,[],[f526,f37])).
% 1.66/0.58  fof(f37,plain,(
% 1.66/0.58    ~r1_tarski(sK0,sK1)),
% 1.66/0.58    inference(cnf_transformation,[],[f28])).
% 1.66/0.58  fof(f28,plain,(
% 1.66/0.58    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.66/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f27])).
% 1.66/0.58  fof(f27,plain,(
% 1.66/0.58    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f16,plain,(
% 1.66/0.58    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.66/0.58    inference(flattening,[],[f15])).
% 1.66/0.58  fof(f15,plain,(
% 1.66/0.58    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.66/0.58    inference(ennf_transformation,[],[f14])).
% 1.66/0.58  fof(f14,negated_conjecture,(
% 1.66/0.58    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.66/0.58    inference(negated_conjecture,[],[f13])).
% 1.66/0.58  fof(f13,conjecture,(
% 1.66/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 1.66/0.58  fof(f526,plain,(
% 1.66/0.58    r1_tarski(sK0,sK1)),
% 1.66/0.58    inference(resolution,[],[f516,f105])).
% 1.66/0.58  fof(f105,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f95,f88])).
% 1.66/0.58  fof(f88,plain,(
% 1.66/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.58    inference(trivial_inequality_removal,[],[f85])).
% 1.66/0.58  fof(f85,plain,(
% 1.66/0.58    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.58    inference(superposition,[],[f55,f60])).
% 1.66/0.58  fof(f60,plain,(
% 1.66/0.58    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 1.66/0.58    inference(resolution,[],[f38,f53])).
% 1.66/0.58  fof(f53,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.66/0.58    inference(definition_unfolding,[],[f40,f41])).
% 1.66/0.58  fof(f41,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f9])).
% 1.66/0.58  % (12138)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.66/0.58  fof(f9,axiom,(
% 1.66/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.66/0.58  fof(f40,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f5])).
% 1.66/0.58  fof(f5,axiom,(
% 1.66/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.66/0.58  fof(f38,plain,(
% 1.66/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.66/0.58    inference(cnf_transformation,[],[f17])).
% 1.66/0.58  fof(f17,plain,(
% 1.66/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.66/0.58    inference(ennf_transformation,[],[f6])).
% 1.66/0.58  fof(f6,axiom,(
% 1.66/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.66/0.58  fof(f55,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.66/0.58    inference(definition_unfolding,[],[f47,f41])).
% 1.66/0.58  fof(f47,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.66/0.58    inference(cnf_transformation,[],[f31])).
% 1.66/0.58  fof(f31,plain,(
% 1.66/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.66/0.58    inference(nnf_transformation,[],[f2])).
% 1.66/0.58  fof(f2,axiom,(
% 1.66/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.66/0.58  fof(f95,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_subset_1(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.66/0.58    inference(extensionality_resolution,[],[f46,f55])).
% 1.66/0.58  fof(f46,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f30])).
% 1.66/0.58  fof(f30,plain,(
% 1.66/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.58    inference(flattening,[],[f29])).
% 1.66/0.58  fof(f29,plain,(
% 1.66/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.58    inference(nnf_transformation,[],[f1])).
% 1.66/0.58  % (12145)Refutation not found, incomplete strategy% (12145)------------------------------
% 1.66/0.58  % (12145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (12145)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (12145)Memory used [KB]: 10746
% 1.66/0.58  % (12145)Time elapsed: 0.166 s
% 1.66/0.58  % (12145)------------------------------
% 1.66/0.58  % (12145)------------------------------
% 1.66/0.58  fof(f1,axiom,(
% 1.66/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.58  % (12144)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.66/0.58  fof(f516,plain,(
% 1.66/0.58    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)),
% 1.66/0.58    inference(forward_demodulation,[],[f515,f461])).
% 1.66/0.58  fof(f461,plain,(
% 1.66/0.58    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 1.66/0.58    inference(forward_demodulation,[],[f453,f75])).
% 1.66/0.58  fof(f75,plain,(
% 1.66/0.58    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.66/0.58    inference(resolution,[],[f54,f57])).
% 1.66/0.58  fof(f57,plain,(
% 1.66/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.58    inference(equality_resolution,[],[f45])).
% 1.66/0.58  fof(f45,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.58    inference(cnf_transformation,[],[f30])).
% 1.66/0.58  fof(f54,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.66/0.58    inference(definition_unfolding,[],[f48,f41])).
% 1.66/0.58  fof(f48,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f31])).
% 1.66/0.58  fof(f453,plain,(
% 1.66/0.58    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X2,X2))) )),
% 1.66/0.58    inference(superposition,[],[f180,f75])).
% 1.66/0.58  fof(f180,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f179,f32])).
% 1.66/0.58  fof(f32,plain,(
% 1.66/0.58    v1_relat_1(sK2)),
% 1.66/0.58    inference(cnf_transformation,[],[f28])).
% 1.66/0.58  fof(f179,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 1.66/0.58    inference(resolution,[],[f51,f33])).
% 1.66/0.58  fof(f33,plain,(
% 1.66/0.58    v1_funct_1(sK2)),
% 1.66/0.58    inference(cnf_transformation,[],[f28])).
% 1.66/0.58  fof(f51,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f24])).
% 1.66/0.58  fof(f24,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/0.58    inference(flattening,[],[f23])).
% 1.66/0.58  fof(f23,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.66/0.58    inference(ennf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.66/0.59  fof(f515,plain,(
% 1.66/0.59    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))),
% 1.66/0.59    inference(subsumption_resolution,[],[f514,f32])).
% 1.66/0.59  fof(f514,plain,(
% 1.66/0.59    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) | ~v1_relat_1(sK2)),
% 1.66/0.59    inference(subsumption_resolution,[],[f512,f238])).
% 1.66/0.59  fof(f238,plain,(
% 1.66/0.59    ( ! [X8] : (r1_tarski(k6_subset_1(sK0,X8),k1_relat_1(sK2))) )),
% 1.66/0.59    inference(superposition,[],[f176,f66])).
% 1.66/0.59  fof(f66,plain,(
% 1.66/0.59    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2))),
% 1.66/0.59    inference(resolution,[],[f43,f35])).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f20])).
% 1.66/0.59  fof(f20,plain,(
% 1.66/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f4])).
% 1.66/0.59  fof(f4,axiom,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.66/0.59  fof(f176,plain,(
% 1.66/0.59    ( ! [X6,X7,X5] : (r1_tarski(k6_subset_1(X5,X6),k2_xboole_0(X5,X7))) )),
% 1.66/0.59    inference(superposition,[],[f68,f64])).
% 1.66/0.59  fof(f64,plain,(
% 1.66/0.59    ( ! [X4,X3] : (k2_xboole_0(k6_subset_1(X3,X4),X3) = X3) )),
% 1.66/0.59    inference(resolution,[],[f43,f53])).
% 1.66/0.59  fof(f68,plain,(
% 1.66/0.59    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 1.66/0.59    inference(resolution,[],[f50,f39])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.66/0.59  fof(f50,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f22])).
% 1.66/0.59  fof(f22,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.66/0.59    inference(ennf_transformation,[],[f3])).
% 1.66/0.59  fof(f3,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.66/0.59  fof(f512,plain,(
% 1.66/0.59    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) | ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.66/0.59    inference(superposition,[],[f42,f491])).
% 1.66/0.59  fof(f491,plain,(
% 1.66/0.59    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.66/0.59    inference(superposition,[],[f211,f78])).
% 1.66/0.59  fof(f78,plain,(
% 1.66/0.59    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.66/0.59    inference(resolution,[],[f54,f34])).
% 1.66/0.59  fof(f34,plain,(
% 1.66/0.59    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  fof(f211,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 1.66/0.59    inference(subsumption_resolution,[],[f210,f32])).
% 1.66/0.59  fof(f210,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 1.66/0.59    inference(subsumption_resolution,[],[f209,f33])).
% 1.66/0.59  fof(f209,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.66/0.59    inference(resolution,[],[f52,f36])).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    v2_funct_1(sK2)),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  fof(f52,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f26])).
% 1.66/0.59  fof(f26,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/0.59    inference(flattening,[],[f25])).
% 1.66/0.59  fof(f25,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.66/0.59    inference(ennf_transformation,[],[f10])).
% 1.66/0.59  fof(f10,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.66/0.59  fof(f42,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f19])).
% 1.66/0.59  fof(f19,plain,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(flattening,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f12])).
% 1.66/0.59  fof(f12,axiom,(
% 1.66/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.66/0.59  % SZS output end Proof for theBenchmark
% 1.66/0.59  % (12139)------------------------------
% 1.66/0.59  % (12139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (12139)Termination reason: Refutation
% 1.66/0.59  
% 1.66/0.59  % (12139)Memory used [KB]: 11001
% 1.66/0.59  % (12139)Time elapsed: 0.081 s
% 1.66/0.59  % (12139)------------------------------
% 1.66/0.59  % (12139)------------------------------
% 1.66/0.59  % (12132)Success in time 0.233 s
%------------------------------------------------------------------------------
