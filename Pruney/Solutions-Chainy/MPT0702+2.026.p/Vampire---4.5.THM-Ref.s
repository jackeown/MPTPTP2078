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
% DateTime   : Thu Dec  3 12:54:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 197 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  184 ( 812 expanded)
%              Number of equality atoms :   35 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(subsumption_resolution,[],[f303,f81])).

fof(f81,plain,(
    ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f59,plain,(
    k1_xboole_0 != k6_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f34,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24])).

fof(f24,plain,
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

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f303,plain,(
    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f302,f275])).

fof(f275,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f130,f203])).

fof(f203,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f193,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f52,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f37])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f193,plain,(
    ! [X6] : k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(X6,X6)) ),
    inference(superposition,[],[f74,f55])).

fof(f74,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f29,f30,f33,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f33,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f130,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f102,f73,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f29,f30,f33,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f102,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f68,f55])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f36,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f302,plain,(
    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f301,f29])).

fof(f301,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f289,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f32,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f32,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f289,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f38,f173])).

fof(f173,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f172,f29])).

fof(f172,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f171,f30])).

fof(f171,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f163,f33])).

fof(f163,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f58,f47])).

fof(f58,plain,(
    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f48])).

fof(f31,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:27:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (14733)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (14741)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (14730)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (14743)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (14752)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (14728)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (14740)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (14739)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (14734)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (14731)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (14735)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (14750)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (14738)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (14748)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (14729)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (14729)Refutation not found, incomplete strategy% (14729)------------------------------
% 0.20/0.54  % (14729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14729)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14729)Memory used [KB]: 1663
% 0.20/0.54  % (14729)Time elapsed: 0.124 s
% 0.20/0.54  % (14729)------------------------------
% 0.20/0.54  % (14729)------------------------------
% 0.20/0.54  % (14753)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (14732)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (14740)Refutation not found, incomplete strategy% (14740)------------------------------
% 0.20/0.54  % (14740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14740)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14740)Memory used [KB]: 10618
% 0.20/0.54  % (14740)Time elapsed: 0.108 s
% 0.20/0.54  % (14740)------------------------------
% 0.20/0.54  % (14740)------------------------------
% 0.20/0.54  % (14756)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (14759)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (14732)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (14747)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (14758)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (14749)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (14751)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (14754)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (14758)Refutation not found, incomplete strategy% (14758)------------------------------
% 0.20/0.55  % (14758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14742)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (14736)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (14738)Refutation not found, incomplete strategy% (14738)------------------------------
% 0.20/0.55  % (14738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14738)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14738)Memory used [KB]: 10746
% 0.20/0.55  % (14738)Time elapsed: 0.148 s
% 0.20/0.55  % (14738)------------------------------
% 0.20/0.55  % (14738)------------------------------
% 0.20/0.56  % (14745)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.56  % (14745)Refutation not found, incomplete strategy% (14745)------------------------------
% 0.20/0.56  % (14745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (14745)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (14745)Memory used [KB]: 10618
% 0.20/0.56  % (14745)Time elapsed: 0.137 s
% 0.20/0.56  % (14745)------------------------------
% 0.20/0.56  % (14745)------------------------------
% 1.54/0.56  % (14737)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  fof(f304,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(subsumption_resolution,[],[f303,f81])).
% 1.54/0.56  fof(f81,plain,(
% 1.54/0.56    ~r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f59,f35])).
% 1.54/0.56  fof(f35,plain,(
% 1.54/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f15])).
% 1.54/0.56  fof(f15,plain,(
% 1.54/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.54/0.56    inference(ennf_transformation,[],[f4])).
% 1.54/0.56  fof(f4,axiom,(
% 1.54/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.54/0.56  fof(f59,plain,(
% 1.54/0.56    k1_xboole_0 != k6_subset_1(sK0,sK1)),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f34,f49])).
% 1.54/0.56  fof(f49,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f43,f37])).
% 1.54/0.56  fof(f37,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.54/0.56  fof(f43,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f28])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.54/0.56    inference(nnf_transformation,[],[f2])).
% 1.54/0.56  fof(f2,axiom,(
% 1.54/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ~r1_tarski(sK0,sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f25])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24])).
% 1.54/0.56  fof(f24,plain,(
% 1.54/0.56    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f14,plain,(
% 1.54/0.56    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.54/0.56    inference(flattening,[],[f13])).
% 1.54/0.56  fof(f13,plain,(
% 1.54/0.56    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.54/0.56    inference(ennf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,negated_conjecture,(
% 1.54/0.56    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.54/0.56    inference(negated_conjecture,[],[f11])).
% 1.54/0.56  fof(f11,conjecture,(
% 1.54/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 1.54/0.56  fof(f303,plain,(
% 1.54/0.56    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)),
% 1.54/0.56    inference(forward_demodulation,[],[f302,f275])).
% 1.54/0.56  fof(f275,plain,(
% 1.54/0.56    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 1.54/0.56    inference(forward_demodulation,[],[f130,f203])).
% 1.54/0.56  fof(f203,plain,(
% 1.54/0.56    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.54/0.56    inference(forward_demodulation,[],[f193,f55])).
% 1.54/0.56  fof(f55,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f52,f48])).
% 1.54/0.56  fof(f48,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f44,f37])).
% 1.54/0.56  fof(f44,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f28])).
% 1.54/0.56  fof(f52,plain,(
% 1.54/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.54/0.56    inference(equality_resolution,[],[f41])).
% 1.54/0.56  fof(f41,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f27,plain,(
% 1.54/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.56    inference(flattening,[],[f26])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.56    inference(nnf_transformation,[],[f1])).
% 1.54/0.56  fof(f1,axiom,(
% 1.54/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.56  fof(f193,plain,(
% 1.54/0.56    ( ! [X6] : (k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(X6,X6))) )),
% 1.54/0.56    inference(superposition,[],[f74,f55])).
% 1.54/0.56  fof(f74,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f29,f30,f33,f47])).
% 1.54/0.56  fof(f47,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f23])).
% 1.54/0.56  fof(f23,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.56    inference(flattening,[],[f22])).
% 1.54/0.56  fof(f22,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.54/0.56    inference(ennf_transformation,[],[f8])).
% 1.54/0.56  fof(f8,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.54/0.56  fof(f33,plain,(
% 1.54/0.56    v2_funct_1(sK2)),
% 1.54/0.56    inference(cnf_transformation,[],[f25])).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    v1_funct_1(sK2)),
% 1.54/0.56    inference(cnf_transformation,[],[f25])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    v1_relat_1(sK2)),
% 1.54/0.56    inference(cnf_transformation,[],[f25])).
% 1.54/0.56  fof(f130,plain,(
% 1.54/0.56    k1_xboole_0 = k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0))),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f102,f73,f42])).
% 1.54/0.56  fof(f42,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f73,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) )),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f29,f30,f33,f39])).
% 1.54/0.56  fof(f39,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f19])).
% 1.54/0.56  fof(f19,plain,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(flattening,[],[f18])).
% 1.54/0.56  fof(f18,plain,(
% 1.54/0.56    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.54/0.56    inference(ennf_transformation,[],[f10])).
% 1.54/0.56  fof(f10,axiom,(
% 1.54/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.54/0.56  fof(f102,plain,(
% 1.54/0.56    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f68,f55])).
% 1.54/0.56  fof(f68,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X0),X1)) )),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f36,f51])).
% 1.54/0.56  fof(f51,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f46,f37])).
% 1.54/0.56  fof(f46,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f21])).
% 1.54/0.56  fof(f21,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.54/0.56    inference(ennf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.54/0.56  fof(f36,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.54/0.56  fof(f302,plain,(
% 1.54/0.56    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))),
% 1.54/0.56    inference(subsumption_resolution,[],[f301,f29])).
% 1.54/0.56  fof(f301,plain,(
% 1.54/0.56    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) | ~v1_relat_1(sK2)),
% 1.54/0.56    inference(subsumption_resolution,[],[f289,f63])).
% 1.54/0.56  fof(f63,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2))) )),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f32,f50])).
% 1.54/0.56  fof(f50,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f45,f37])).
% 1.54/0.56  fof(f45,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f20])).
% 1.54/0.56  fof(f20,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f3])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.54/0.56    inference(cnf_transformation,[],[f25])).
% 1.54/0.56  fof(f289,plain,(
% 1.54/0.56    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) | ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.54/0.56    inference(superposition,[],[f38,f173])).
% 1.54/0.56  fof(f173,plain,(
% 1.54/0.56    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.54/0.56    inference(subsumption_resolution,[],[f172,f29])).
% 1.54/0.56  fof(f172,plain,(
% 1.54/0.56    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~v1_relat_1(sK2)),
% 1.54/0.56    inference(subsumption_resolution,[],[f171,f30])).
% 1.54/0.56  fof(f171,plain,(
% 1.54/0.56    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.54/0.56    inference(subsumption_resolution,[],[f163,f33])).
% 1.54/0.56  fof(f163,plain,(
% 1.54/0.56    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.54/0.56    inference(superposition,[],[f58,f47])).
% 1.54/0.56  fof(f58,plain,(
% 1.54/0.56    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.54/0.56    inference(unit_resulting_resolution,[],[f31,f48])).
% 1.54/0.56  fof(f31,plain,(
% 1.54/0.56    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.54/0.56    inference(cnf_transformation,[],[f25])).
% 1.54/0.56  fof(f38,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f17])).
% 1.54/0.56  fof(f17,plain,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(flattening,[],[f16])).
% 1.54/0.56  fof(f16,plain,(
% 1.54/0.56    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f9])).
% 1.54/0.56  fof(f9,axiom,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.54/0.56  % SZS output end Proof for theBenchmark
% 1.54/0.56  % (14732)------------------------------
% 1.54/0.56  % (14732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (14732)Termination reason: Refutation
% 1.54/0.56  
% 1.54/0.56  % (14732)Memory used [KB]: 1918
% 1.54/0.56  % (14732)Time elapsed: 0.131 s
% 1.54/0.56  % (14732)------------------------------
% 1.54/0.56  % (14732)------------------------------
% 1.54/0.56  % (14746)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.54/0.56  % (14758)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  % (14725)Success in time 0.197 s
%------------------------------------------------------------------------------
