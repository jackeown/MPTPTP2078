%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:08 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 134 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  178 ( 414 expanded)
%              Number of equality atoms :   44 (  65 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f960,plain,(
    $false ),
    inference(resolution,[],[f941,f44])).

fof(f44,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f941,plain,(
    ! [X13] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X13)),X13) ),
    inference(trivial_inequality_removal,[],[f926])).

fof(f926,plain,(
    ! [X13] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X13)),X13) ) ),
    inference(superposition,[],[f66,f908])).

fof(f908,plain,(
    ! [X16] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16) ),
    inference(subsumption_resolution,[],[f907,f41])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f907,plain,(
    ! [X16] :
      ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f906,f218])).

fof(f218,plain,(
    ! [X2,X3] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1)) ),
    inference(resolution,[],[f208,f64])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(sK1,X1))
      | r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f202,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f202,plain,(
    ! [X1] : r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f66,f193])).

fof(f193,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f76,f41])).

fof(f76,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | k1_xboole_0 = k6_subset_1(k10_relat_1(X4,X5),k1_relat_1(X4)) ) ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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

fof(f906,plain,(
    ! [X16] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16),k1_relat_1(sK1))
      | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f893,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f893,plain,(
    ! [X16] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16),k1_relat_1(sK1))
      | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f213,f622])).

fof(f622,plain,(
    ! [X1] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)) ),
    inference(superposition,[],[f619,f358])).

fof(f358,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f357,f41])).

fof(f357,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f356,f42])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f356,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f59,f43])).

fof(f43,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f619,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f618,f41])).

fof(f618,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f118,f42])).

fof(f118,plain,(
    ! [X8,X9] :
      ( ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(X8,k10_relat_1(X8,X9)),X9) ) ),
    inference(resolution,[],[f52,f65])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | k1_xboole_0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f211,f45])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k9_relat_1(X0,X1))
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | k1_xboole_0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(extensionality_resolution,[],[f55,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (30057)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (30065)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (30049)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (30051)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (30048)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (30059)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (30047)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (30054)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.58  % (30067)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.59  % (30044)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.59  % (30042)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.59  % (30046)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.59  % (30043)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.60  % (30053)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.61  % (30052)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.61  % (30064)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.95/0.62  % (30058)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.95/0.62  % (30060)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.95/0.62  % (30071)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.95/0.62  % (30045)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.95/0.62  % (30066)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.95/0.62  % (30050)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.95/0.63  % (30063)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.95/0.63  % (30056)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.95/0.63  % (30062)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.16/0.64  % (30061)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.16/0.64  % (30055)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.16/0.64  % (30069)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.16/0.64  % (30070)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.16/0.64  % (30058)Refutation not found, incomplete strategy% (30058)------------------------------
% 2.16/0.64  % (30058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.64  % (30058)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.64  
% 2.16/0.64  % (30058)Memory used [KB]: 10618
% 2.16/0.64  % (30058)Time elapsed: 0.206 s
% 2.16/0.64  % (30058)------------------------------
% 2.16/0.64  % (30058)------------------------------
% 2.16/0.64  % (30068)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.22/0.65  % (30048)Refutation found. Thanks to Tanya!
% 2.22/0.65  % SZS status Theorem for theBenchmark
% 2.22/0.65  % SZS output start Proof for theBenchmark
% 2.22/0.65  fof(f960,plain,(
% 2.22/0.65    $false),
% 2.22/0.65    inference(resolution,[],[f941,f44])).
% 2.22/0.65  fof(f44,plain,(
% 2.22/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f35])).
% 2.22/0.65  fof(f35,plain,(
% 2.22/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f34])).
% 2.22/0.65  fof(f34,plain,(
% 2.22/0.65    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f18,plain,(
% 2.22/0.65    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.22/0.65    inference(flattening,[],[f17])).
% 2.22/0.65  fof(f17,plain,(
% 2.22/0.65    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.22/0.65    inference(ennf_transformation,[],[f16])).
% 2.22/0.65  fof(f16,negated_conjecture,(
% 2.22/0.65    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.22/0.65    inference(negated_conjecture,[],[f15])).
% 2.22/0.65  fof(f15,conjecture,(
% 2.22/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 2.22/0.65  fof(f941,plain,(
% 2.22/0.65    ( ! [X13] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X13)),X13)) )),
% 2.22/0.65    inference(trivial_inequality_removal,[],[f926])).
% 2.22/0.65  fof(f926,plain,(
% 2.22/0.65    ( ! [X13] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X13)),X13)) )),
% 2.22/0.65    inference(superposition,[],[f66,f908])).
% 2.22/0.65  fof(f908,plain,(
% 2.22/0.65    ( ! [X16] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16)) )),
% 2.22/0.65    inference(subsumption_resolution,[],[f907,f41])).
% 2.22/0.65  fof(f41,plain,(
% 2.22/0.65    v1_relat_1(sK1)),
% 2.22/0.65    inference(cnf_transformation,[],[f35])).
% 2.22/0.65  fof(f907,plain,(
% 2.22/0.65    ( ! [X16] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16) | ~v1_relat_1(sK1)) )),
% 2.22/0.65    inference(subsumption_resolution,[],[f906,f218])).
% 2.22/0.65  fof(f218,plain,(
% 2.22/0.65    ( ! [X2,X3] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))) )),
% 2.22/0.65    inference(resolution,[],[f208,f64])).
% 2.22/0.65  fof(f64,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.22/0.65    inference(definition_unfolding,[],[f47,f48])).
% 2.22/0.65  fof(f48,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f8])).
% 2.22/0.65  fof(f8,axiom,(
% 2.22/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.22/0.65  fof(f47,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f6])).
% 2.22/0.65  fof(f6,axiom,(
% 2.22/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.22/0.65  fof(f208,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r1_tarski(X0,k10_relat_1(sK1,X1)) | r1_tarski(X0,k1_relat_1(sK1))) )),
% 2.22/0.65    inference(resolution,[],[f202,f60])).
% 2.22/0.65  fof(f60,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f31])).
% 2.22/0.65  fof(f31,plain,(
% 2.22/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.22/0.65    inference(flattening,[],[f30])).
% 2.22/0.65  fof(f30,plain,(
% 2.22/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.22/0.65    inference(ennf_transformation,[],[f4])).
% 2.22/0.65  fof(f4,axiom,(
% 2.22/0.65    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.22/0.65  fof(f202,plain,(
% 2.22/0.65    ( ! [X1] : (r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1))) )),
% 2.22/0.65    inference(trivial_inequality_removal,[],[f195])).
% 2.22/0.65  fof(f195,plain,(
% 2.22/0.65    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,X1),k1_relat_1(sK1))) )),
% 2.22/0.65    inference(superposition,[],[f66,f193])).
% 2.22/0.65  fof(f193,plain,(
% 2.22/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.22/0.65    inference(resolution,[],[f76,f41])).
% 2.22/0.65  fof(f76,plain,(
% 2.22/0.65    ( ! [X4,X5] : (~v1_relat_1(X4) | k1_xboole_0 = k6_subset_1(k10_relat_1(X4,X5),k1_relat_1(X4))) )),
% 2.22/0.65    inference(resolution,[],[f65,f49])).
% 2.22/0.65  fof(f49,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f20])).
% 2.22/0.65  fof(f20,plain,(
% 2.22/0.65    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.22/0.65    inference(ennf_transformation,[],[f10])).
% 2.22/0.65  fof(f10,axiom,(
% 2.22/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.22/0.65  fof(f65,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 2.22/0.65    inference(definition_unfolding,[],[f57,f48])).
% 2.22/0.65  fof(f57,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f38])).
% 2.22/0.65  fof(f38,plain,(
% 2.22/0.65    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.22/0.65    inference(nnf_transformation,[],[f2])).
% 2.22/0.65  fof(f2,axiom,(
% 2.22/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.22/0.65  fof(f906,plain,(
% 2.22/0.65    ( ! [X16] : (~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16),k1_relat_1(sK1)) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16) | ~v1_relat_1(sK1)) )),
% 2.22/0.65    inference(subsumption_resolution,[],[f893,f45])).
% 2.22/0.65  fof(f45,plain,(
% 2.22/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f5])).
% 2.22/0.65  fof(f5,axiom,(
% 2.22/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.22/0.65  fof(f893,plain,(
% 2.22/0.65    ( ! [X16] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16),k1_relat_1(sK1)) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X16)),X16) | ~v1_relat_1(sK1)) )),
% 2.22/0.65    inference(superposition,[],[f213,f622])).
% 2.22/0.65  fof(f622,plain,(
% 2.22/0.65    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1))) )),
% 2.22/0.65    inference(superposition,[],[f619,f358])).
% 2.22/0.65  fof(f358,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 2.22/0.65    inference(subsumption_resolution,[],[f357,f41])).
% 2.22/0.65  fof(f357,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 2.22/0.65    inference(subsumption_resolution,[],[f356,f42])).
% 2.22/0.65  fof(f42,plain,(
% 2.22/0.65    v1_funct_1(sK1)),
% 2.22/0.65    inference(cnf_transformation,[],[f35])).
% 2.22/0.65  fof(f356,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.22/0.65    inference(resolution,[],[f59,f43])).
% 2.22/0.65  fof(f43,plain,(
% 2.22/0.65    v2_funct_1(sK1)),
% 2.22/0.65    inference(cnf_transformation,[],[f35])).
% 2.22/0.65  fof(f59,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f29])).
% 2.22/0.65  fof(f29,plain,(
% 2.22/0.65    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.22/0.65    inference(flattening,[],[f28])).
% 2.22/0.65  fof(f28,plain,(
% 2.22/0.65    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.22/0.65    inference(ennf_transformation,[],[f12])).
% 2.22/0.65  fof(f12,axiom,(
% 2.22/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 2.22/0.65  fof(f619,plain,(
% 2.22/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 2.22/0.65    inference(subsumption_resolution,[],[f618,f41])).
% 2.22/0.65  fof(f618,plain,(
% 2.22/0.65    ( ! [X0] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 2.22/0.65    inference(resolution,[],[f118,f42])).
% 2.22/0.65  fof(f118,plain,(
% 2.22/0.65    ( ! [X8,X9] : (~v1_funct_1(X8) | ~v1_relat_1(X8) | k1_xboole_0 = k6_subset_1(k9_relat_1(X8,k10_relat_1(X8,X9)),X9)) )),
% 2.22/0.65    inference(resolution,[],[f52,f65])).
% 2.22/0.65  fof(f52,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f26])).
% 2.22/0.65  fof(f26,plain,(
% 2.22/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.22/0.65    inference(flattening,[],[f25])).
% 2.22/0.65  fof(f25,plain,(
% 2.22/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.22/0.65    inference(ennf_transformation,[],[f13])).
% 2.22/0.65  fof(f13,axiom,(
% 2.22/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 2.22/0.65  fof(f213,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(X0,X1),k1_xboole_0) | ~r1_tarski(X1,k1_relat_1(X0)) | k1_xboole_0 = X1 | ~v1_relat_1(X0)) )),
% 2.22/0.65    inference(subsumption_resolution,[],[f211,f45])).
% 2.22/0.65  fof(f211,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k9_relat_1(X0,X1)) | ~r1_tarski(X1,k1_relat_1(X0)) | k1_xboole_0 = X1 | ~v1_relat_1(X0)) )),
% 2.22/0.65    inference(extensionality_resolution,[],[f55,f51])).
% 2.22/0.65  fof(f51,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f24])).
% 2.22/0.65  fof(f24,plain,(
% 2.22/0.65    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 2.22/0.65    inference(flattening,[],[f23])).
% 2.22/0.65  fof(f23,plain,(
% 2.22/0.65    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 2.22/0.65    inference(ennf_transformation,[],[f9])).
% 2.22/0.65  fof(f9,axiom,(
% 2.22/0.65    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 2.22/0.65  fof(f55,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f37])).
% 2.22/0.65  fof(f37,plain,(
% 2.22/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.65    inference(flattening,[],[f36])).
% 2.22/0.65  fof(f36,plain,(
% 2.22/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.65    inference(nnf_transformation,[],[f1])).
% 2.22/0.65  fof(f1,axiom,(
% 2.22/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.22/0.65  fof(f66,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(definition_unfolding,[],[f56,f48])).
% 2.22/0.65  fof(f56,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.22/0.65    inference(cnf_transformation,[],[f38])).
% 2.22/0.65  % SZS output end Proof for theBenchmark
% 2.22/0.65  % (30048)------------------------------
% 2.22/0.65  % (30048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.65  % (30048)Termination reason: Refutation
% 2.22/0.65  
% 2.22/0.65  % (30048)Memory used [KB]: 11129
% 2.22/0.65  % (30048)Time elapsed: 0.223 s
% 2.22/0.65  % (30048)------------------------------
% 2.22/0.65  % (30048)------------------------------
% 2.22/0.65  % (30041)Success in time 0.286 s
%------------------------------------------------------------------------------
