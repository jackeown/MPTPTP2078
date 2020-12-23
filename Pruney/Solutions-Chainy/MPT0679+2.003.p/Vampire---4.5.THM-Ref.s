%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:28 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 308 expanded)
%              Number of leaves         :   14 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 511 expanded)
%              Number of equality atoms :   35 ( 235 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f459,plain,(
    $false ),
    inference(subsumption_resolution,[],[f458,f69])).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f67,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f67,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(forward_demodulation,[],[f59,f55])).

fof(f55,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f40,f40,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f39,f40,f40])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f46,f40,f52])).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f458,plain,(
    ~ r1_xboole_0(k1_xboole_0,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f457,f70])).

fof(f70,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( v2_funct_1(X2)
         => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f457,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,k1_xboole_0),k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f456,f211])).

fof(f211,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(X0,X1)) ),
    inference(backward_demodulation,[],[f92,f203])).

fof(f203,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(k6_subset_1(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f64,f143,f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f143,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),X1)) ),
    inference(unit_resulting_resolution,[],[f65,f67,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_subset_1(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f40])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f51,f40])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f92,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),X1)) ),
    inference(unit_resulting_resolution,[],[f67,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f456,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f455,f203])).

fof(f455,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(k6_subset_1(sK0,sK1),sK1))),k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f449,f181])).

fof(f181,plain,(
    ! [X0,X1] : k6_subset_1(k9_relat_1(sK2,X0),k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f31,f29,f30,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(X2,X0),k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f44,f52,f52])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f449,plain,(
    ~ r1_xboole_0(k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f415,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(k6_subset_1(X0,k6_subset_1(X0,X1)),X1) ) ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f415,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f414,f302])).

fof(f302,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X0)) ),
    inference(superposition,[],[f278,f55])).

fof(f278,plain,(
    ! [X12,X13] : r1_tarski(k9_relat_1(sK2,k6_subset_1(X12,k6_subset_1(X12,X13))),k9_relat_1(sK2,X12)) ),
    inference(superposition,[],[f64,f181])).

fof(f414,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f412,f162])).

fof(f162,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f29,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

fof(f412,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f80,f60])).

fof(f80,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(extensionality_resolution,[],[f37,f32])).

fof(f32,plain,(
    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:17:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.19/0.54  % (12527)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.19/0.55  % (12537)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.19/0.55  % (12529)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.19/0.55  % (12545)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.51/0.56  % (12519)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.51/0.56  % (12529)Refutation not found, incomplete strategy% (12529)------------------------------
% 1.51/0.56  % (12529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (12532)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.51/0.57  % (12529)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (12529)Memory used [KB]: 10746
% 1.51/0.57  % (12529)Time elapsed: 0.136 s
% 1.51/0.57  % (12529)------------------------------
% 1.51/0.57  % (12529)------------------------------
% 1.51/0.57  % (12524)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.51/0.58  % (12536)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.51/0.58  % (12534)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.51/0.58  % (12538)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.51/0.58  % (12521)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.51/0.58  % (12520)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.51/0.58  % (12548)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.51/0.58  % (12531)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.51/0.58  % (12542)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.51/0.58  % (12530)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.51/0.59  % (12523)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.51/0.59  % (12540)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.51/0.59  % (12541)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.51/0.59  % (12546)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.51/0.59  % (12525)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.59  % (12522)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.51/0.59  % (12533)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.51/0.60  % (12547)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.51/0.60  % (12535)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.51/0.60  % (12547)Refutation not found, incomplete strategy% (12547)------------------------------
% 1.51/0.60  % (12547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.60  % (12547)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.60  
% 1.51/0.60  % (12547)Memory used [KB]: 10746
% 1.51/0.60  % (12547)Time elapsed: 0.175 s
% 1.51/0.60  % (12547)------------------------------
% 1.51/0.60  % (12547)------------------------------
% 1.51/0.60  % (12526)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.51/0.60  % (12539)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.51/0.60  % (12528)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.51/0.61  % (12543)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.51/0.62  % (12544)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.51/0.62  % (12535)Refutation not found, incomplete strategy% (12535)------------------------------
% 1.51/0.62  % (12535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.62  % (12535)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.62  
% 1.51/0.62  % (12535)Memory used [KB]: 10618
% 1.51/0.62  % (12535)Time elapsed: 0.197 s
% 1.51/0.62  % (12535)------------------------------
% 1.51/0.62  % (12535)------------------------------
% 1.51/0.62  % (12538)Refutation found. Thanks to Tanya!
% 1.51/0.62  % SZS status Theorem for theBenchmark
% 1.51/0.63  % SZS output start Proof for theBenchmark
% 1.51/0.63  fof(f459,plain,(
% 1.51/0.63    $false),
% 1.51/0.63    inference(subsumption_resolution,[],[f458,f69])).
% 1.51/0.63  fof(f69,plain,(
% 1.51/0.63    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.51/0.63    inference(superposition,[],[f67,f56])).
% 1.51/0.64  fof(f56,plain,(
% 1.51/0.64    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 1.51/0.64    inference(definition_unfolding,[],[f42,f40])).
% 1.51/0.64  fof(f40,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f12])).
% 1.51/0.64  fof(f12,axiom,(
% 1.51/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.51/0.64  fof(f42,plain,(
% 1.51/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f8])).
% 1.51/0.64  fof(f8,axiom,(
% 1.51/0.64    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.51/0.64  fof(f67,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 1.51/0.64    inference(forward_demodulation,[],[f59,f55])).
% 1.51/0.64  fof(f55,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 1.51/0.64    inference(definition_unfolding,[],[f38,f40,f40,f52])).
% 1.51/0.64  fof(f52,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.51/0.64    inference(definition_unfolding,[],[f39,f40,f40])).
% 1.51/0.64  fof(f39,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f7])).
% 1.51/0.64  fof(f7,axiom,(
% 1.51/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.51/0.64  fof(f38,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f6])).
% 1.51/0.64  fof(f6,axiom,(
% 1.51/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.51/0.64  fof(f59,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))),X1)) )),
% 1.51/0.64    inference(definition_unfolding,[],[f46,f40,f52])).
% 1.51/0.64  fof(f46,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f11])).
% 1.51/0.64  fof(f11,axiom,(
% 1.51/0.64    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).
% 1.51/0.64  fof(f458,plain,(
% 1.51/0.64    ~r1_xboole_0(k1_xboole_0,k9_relat_1(sK2,sK1))),
% 1.51/0.64    inference(forward_demodulation,[],[f457,f70])).
% 1.51/0.64  fof(f70,plain,(
% 1.51/0.64    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.51/0.64    inference(unit_resulting_resolution,[],[f29,f41])).
% 1.51/0.64  fof(f41,plain,(
% 1.51/0.64    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f20])).
% 1.51/0.64  fof(f20,plain,(
% 1.51/0.64    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.51/0.64    inference(ennf_transformation,[],[f13])).
% 1.51/0.64  fof(f13,axiom,(
% 1.51/0.64    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 1.51/0.64  fof(f29,plain,(
% 1.51/0.64    v1_relat_1(sK2)),
% 1.51/0.64    inference(cnf_transformation,[],[f19])).
% 1.51/0.64  fof(f19,plain,(
% 1.51/0.64    ? [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1)) & v2_funct_1(X2) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.51/0.64    inference(flattening,[],[f18])).
% 1.51/0.64  fof(f18,plain,(
% 1.51/0.64    ? [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1)) & v2_funct_1(X2)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.51/0.64    inference(ennf_transformation,[],[f17])).
% 1.51/0.64  fof(f17,negated_conjecture,(
% 1.51/0.64    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.51/0.64    inference(negated_conjecture,[],[f16])).
% 1.51/0.64  fof(f16,conjecture,(
% 1.51/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 1.51/0.64  fof(f457,plain,(
% 1.51/0.64    ~r1_xboole_0(k9_relat_1(sK2,k1_xboole_0),k9_relat_1(sK2,sK1))),
% 1.51/0.64    inference(forward_demodulation,[],[f456,f211])).
% 1.51/0.64  fof(f211,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(X0,X1))) )),
% 1.51/0.64    inference(backward_demodulation,[],[f92,f203])).
% 1.51/0.64  fof(f203,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(k6_subset_1(X0,X1),X1)) )),
% 1.51/0.64    inference(unit_resulting_resolution,[],[f64,f143,f37])).
% 1.51/0.64  fof(f37,plain,(
% 1.51/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.51/0.64    inference(cnf_transformation,[],[f2])).
% 1.51/0.64  fof(f2,axiom,(
% 1.51/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.64  fof(f143,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),X1))) )),
% 1.51/0.64    inference(unit_resulting_resolution,[],[f65,f67,f60])).
% 1.51/0.64  fof(f60,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_subset_1(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.51/0.64    inference(definition_unfolding,[],[f47,f40])).
% 1.51/0.64  fof(f47,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f26])).
% 1.51/0.64  fof(f26,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.51/0.64    inference(flattening,[],[f25])).
% 1.51/0.64  fof(f25,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.51/0.64    inference(ennf_transformation,[],[f10])).
% 1.51/0.64  fof(f10,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.51/0.64  fof(f65,plain,(
% 1.51/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.64    inference(equality_resolution,[],[f36])).
% 1.51/0.64  fof(f36,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.51/0.64    inference(cnf_transformation,[],[f2])).
% 1.51/0.64  fof(f64,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.51/0.64    inference(definition_unfolding,[],[f51,f40])).
% 1.51/0.64  fof(f51,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f5])).
% 1.51/0.64  fof(f5,axiom,(
% 1.51/0.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.51/0.64  fof(f92,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),X1))) )),
% 1.51/0.64    inference(unit_resulting_resolution,[],[f67,f53])).
% 1.51/0.64  fof(f53,plain,(
% 1.51/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.51/0.64    inference(definition_unfolding,[],[f34,f52])).
% 1.51/0.64  fof(f34,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f1])).
% 1.51/0.64  fof(f1,axiom,(
% 1.51/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.51/0.64  fof(f456,plain,(
% 1.51/0.64    ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(sK0,sK1))),k9_relat_1(sK2,sK1))),
% 1.51/0.64    inference(forward_demodulation,[],[f455,f203])).
% 1.51/0.64  fof(f455,plain,(
% 1.51/0.64    ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(k6_subset_1(sK0,sK1),sK1))),k9_relat_1(sK2,sK1))),
% 1.51/0.64    inference(forward_demodulation,[],[f449,f181])).
% 1.51/0.64  fof(f181,plain,(
% 1.51/0.64    ( ! [X0,X1] : (k6_subset_1(k9_relat_1(sK2,X0),k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 1.51/0.64    inference(unit_resulting_resolution,[],[f31,f29,f30,f57])).
% 1.51/0.64  fof(f57,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k9_relat_1(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(X2,X0),k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) )),
% 1.51/0.64    inference(definition_unfolding,[],[f44,f52,f52])).
% 1.51/0.64  fof(f44,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f23])).
% 1.51/0.64  fof(f23,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.51/0.64    inference(flattening,[],[f22])).
% 1.51/0.64  fof(f22,plain,(
% 1.51/0.64    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.51/0.64    inference(ennf_transformation,[],[f15])).
% 1.51/0.64  fof(f15,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 1.51/0.64  fof(f30,plain,(
% 1.51/0.64    v1_funct_1(sK2)),
% 1.51/0.64    inference(cnf_transformation,[],[f19])).
% 1.51/0.64  fof(f31,plain,(
% 1.51/0.64    v2_funct_1(sK2)),
% 1.51/0.64    inference(cnf_transformation,[],[f19])).
% 1.51/0.64  fof(f449,plain,(
% 1.51/0.64    ~r1_xboole_0(k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))),
% 1.51/0.64    inference(unit_resulting_resolution,[],[f415,f58])).
% 1.51/0.64  fof(f58,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(k6_subset_1(X0,k6_subset_1(X0,X1)),X1)) )),
% 1.51/0.64    inference(definition_unfolding,[],[f45,f52])).
% 1.51/0.64  fof(f45,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 1.51/0.64    inference(cnf_transformation,[],[f24])).
% 1.51/0.64  fof(f24,plain,(
% 1.51/0.64    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 1.51/0.64    inference(ennf_transformation,[],[f9])).
% 1.51/0.64  fof(f9,axiom,(
% 1.51/0.64    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 1.51/0.64  fof(f415,plain,(
% 1.51/0.64    ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 1.51/0.64    inference(subsumption_resolution,[],[f414,f302])).
% 1.51/0.64  fof(f302,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X0))) )),
% 1.51/0.64    inference(superposition,[],[f278,f55])).
% 1.51/0.64  fof(f278,plain,(
% 1.51/0.64    ( ! [X12,X13] : (r1_tarski(k9_relat_1(sK2,k6_subset_1(X12,k6_subset_1(X12,X13))),k9_relat_1(sK2,X12))) )),
% 1.51/0.64    inference(superposition,[],[f64,f181])).
% 1.51/0.64  fof(f414,plain,(
% 1.51/0.64    ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 1.51/0.64    inference(subsumption_resolution,[],[f412,f162])).
% 1.51/0.64  fof(f162,plain,(
% 1.51/0.64    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1)))) )),
% 1.51/0.64    inference(unit_resulting_resolution,[],[f29,f43])).
% 1.51/0.64  fof(f43,plain,(
% 1.51/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))) )),
% 1.51/0.64    inference(cnf_transformation,[],[f21])).
% 1.51/0.64  fof(f21,plain,(
% 1.51/0.64    ! [X0,X1,X2] : (r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) | ~v1_relat_1(X2))),
% 1.51/0.64    inference(ennf_transformation,[],[f14])).
% 1.51/0.64  fof(f14,axiom,(
% 1.51/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.51/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).
% 1.51/0.64  fof(f412,plain,(
% 1.51/0.64    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 1.51/0.64    inference(resolution,[],[f80,f60])).
% 1.51/0.64  fof(f80,plain,(
% 1.51/0.64    ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) | ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 1.51/0.64    inference(extensionality_resolution,[],[f37,f32])).
% 1.51/0.64  fof(f32,plain,(
% 1.51/0.64    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.51/0.64    inference(cnf_transformation,[],[f19])).
% 1.51/0.64  % SZS output end Proof for theBenchmark
% 1.51/0.64  % (12538)------------------------------
% 1.51/0.64  % (12538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.64  % (12538)Termination reason: Refutation
% 1.51/0.64  
% 1.51/0.64  % (12538)Memory used [KB]: 1918
% 1.51/0.64  % (12538)Time elapsed: 0.193 s
% 1.51/0.64  % (12538)------------------------------
% 1.51/0.64  % (12538)------------------------------
% 1.51/0.64  % (12518)Success in time 0.277 s
%------------------------------------------------------------------------------
