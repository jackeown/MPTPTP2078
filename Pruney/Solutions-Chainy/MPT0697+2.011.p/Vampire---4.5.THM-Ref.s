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
% DateTime   : Thu Dec  3 12:54:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 106 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   18
%              Number of atoms          :  139 ( 347 expanded)
%              Number of equality atoms :   32 (  37 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f505,plain,(
    $false ),
    inference(resolution,[],[f480,f47])).

% (1747)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f47,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f39])).

% (1759)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f39,plain,
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

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f480,plain,(
    ! [X6] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6) ),
    inference(trivial_inequality_removal,[],[f473])).

fof(f473,plain,(
    ! [X6] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6) ) ),
    inference(superposition,[],[f51,f460])).

fof(f460,plain,(
    ! [X12] : k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12) ),
    inference(subsumption_resolution,[],[f459,f44])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f459,plain,(
    ! [X12] :
      ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f443,f126])).

fof(f126,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1)) ),
    inference(resolution,[],[f85,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f85,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,k10_relat_1(sK1,X6))
      | r1_tarski(X5,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f70,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f44,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f443,plain,(
    ! [X12] :
      ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12),k1_relat_1(sK1))
      | k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)
      | ~ v1_relat_1(sK1) ) ),
    inference(trivial_inequality_removal,[],[f442])).

fof(f442,plain,(
    ! [X12] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12),k1_relat_1(sK1))
      | k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f64,f224])).

fof(f224,plain,(
    ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2)) ),
    inference(superposition,[],[f113,f88])).

fof(f88,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2) ),
    inference(resolution,[],[f76,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
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

fof(f76,plain,(
    ! [X2] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2) ),
    inference(subsumption_resolution,[],[f73,f44])).

fof(f73,plain,(
    ! [X2] :
      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f113,plain,(
    ! [X2,X3] : k4_xboole_0(k9_relat_1(sK1,X2),k9_relat_1(sK1,X3)) = k9_relat_1(sK1,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f80,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f80,plain,(
    ! [X0,X1] : k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f79,f66])).

fof(f79,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f78,f44])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f77,f45])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f46,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

% (1749)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f46,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (1752)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.50  % (1754)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (1746)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (1760)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (1762)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (1769)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (1754)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (1740)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (1741)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (1744)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (1743)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (1742)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (1766)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (1770)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (1758)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (1761)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (1756)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (1750)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (1753)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (1751)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (1748)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (1757)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.45/0.54  % SZS output start Proof for theBenchmark
% 1.45/0.54  fof(f505,plain,(
% 1.45/0.54    $false),
% 1.45/0.54    inference(resolution,[],[f480,f47])).
% 1.45/0.54  % (1747)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.45/0.54  fof(f47,plain,(
% 1.45/0.54    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f40])).
% 1.45/0.54  fof(f40,plain,(
% 1.45/0.54    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f39])).
% 1.45/0.54  % (1759)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.45/0.54  fof(f39,plain,(
% 1.45/0.54    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f21,plain,(
% 1.45/0.54    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.45/0.54    inference(flattening,[],[f20])).
% 1.45/0.54  fof(f20,plain,(
% 1.45/0.54    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.45/0.54    inference(ennf_transformation,[],[f19])).
% 1.45/0.54  fof(f19,negated_conjecture,(
% 1.45/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.45/0.54    inference(negated_conjecture,[],[f18])).
% 1.45/0.54  fof(f18,conjecture,(
% 1.45/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.45/0.54  fof(f480,plain,(
% 1.45/0.54    ( ! [X6] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6)) )),
% 1.45/0.54    inference(trivial_inequality_removal,[],[f473])).
% 1.45/0.54  fof(f473,plain,(
% 1.45/0.54    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6)) )),
% 1.45/0.54    inference(superposition,[],[f51,f460])).
% 1.45/0.54  fof(f460,plain,(
% 1.45/0.54    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f459,f44])).
% 1.45/0.54  fof(f44,plain,(
% 1.45/0.54    v1_relat_1(sK1)),
% 1.45/0.54    inference(cnf_transformation,[],[f40])).
% 1.45/0.54  fof(f459,plain,(
% 1.45/0.54    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12) | ~v1_relat_1(sK1)) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f443,f126])).
% 1.45/0.54  fof(f126,plain,(
% 1.45/0.54    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))) )),
% 1.45/0.54    inference(resolution,[],[f85,f57])).
% 1.45/0.54  fof(f57,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f6])).
% 1.45/0.54  fof(f6,axiom,(
% 1.45/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.45/0.54  fof(f85,plain,(
% 1.45/0.54    ( ! [X6,X5] : (~r1_tarski(X5,k10_relat_1(sK1,X6)) | r1_tarski(X5,k1_relat_1(sK1))) )),
% 1.45/0.54    inference(resolution,[],[f70,f48])).
% 1.45/0.54  fof(f48,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f23])).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.45/0.54    inference(flattening,[],[f22])).
% 1.45/0.54  fof(f22,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.45/0.54    inference(ennf_transformation,[],[f4])).
% 1.45/0.54  fof(f4,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.45/0.54  fof(f70,plain,(
% 1.45/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.45/0.54    inference(resolution,[],[f44,f62])).
% 1.45/0.54  fof(f62,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f33])).
% 1.45/0.54  fof(f33,plain,(
% 1.45/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f12])).
% 1.45/0.54  fof(f12,axiom,(
% 1.45/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.45/0.54  fof(f443,plain,(
% 1.45/0.54    ( ! [X12] : (~r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12),k1_relat_1(sK1)) | k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12) | ~v1_relat_1(sK1)) )),
% 1.45/0.54    inference(trivial_inequality_removal,[],[f442])).
% 1.45/0.54  fof(f442,plain,(
% 1.45/0.54    ( ! [X12] : (k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12),k1_relat_1(sK1)) | k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12) | ~v1_relat_1(sK1)) )),
% 1.45/0.54    inference(superposition,[],[f64,f224])).
% 1.45/0.54  fof(f224,plain,(
% 1.45/0.54    ( ! [X2] : (k1_xboole_0 = k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))) )),
% 1.45/0.54    inference(superposition,[],[f113,f88])).
% 1.45/0.54  fof(f88,plain,(
% 1.45/0.54    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2)) )),
% 1.45/0.54    inference(resolution,[],[f76,f52])).
% 1.45/0.54  fof(f52,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.45/0.54    inference(cnf_transformation,[],[f41])).
% 1.45/0.54  fof(f41,plain,(
% 1.45/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.45/0.54    inference(nnf_transformation,[],[f2])).
% 1.45/0.54  fof(f2,axiom,(
% 1.45/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.45/0.54  fof(f76,plain,(
% 1.45/0.54    ( ! [X2] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2)) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f73,f44])).
% 1.45/0.54  fof(f73,plain,(
% 1.45/0.54    ( ! [X2] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2) | ~v1_relat_1(sK1)) )),
% 1.45/0.54    inference(resolution,[],[f45,f56])).
% 1.45/0.54  fof(f56,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f28])).
% 1.45/0.54  fof(f28,plain,(
% 1.45/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.45/0.54    inference(flattening,[],[f27])).
% 1.45/0.54  fof(f27,plain,(
% 1.45/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.45/0.54    inference(ennf_transformation,[],[f17])).
% 1.45/0.54  fof(f17,axiom,(
% 1.45/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.45/0.54  fof(f45,plain,(
% 1.45/0.54    v1_funct_1(sK1)),
% 1.45/0.54    inference(cnf_transformation,[],[f40])).
% 1.45/0.54  fof(f113,plain,(
% 1.45/0.54    ( ! [X2,X3] : (k4_xboole_0(k9_relat_1(sK1,X2),k9_relat_1(sK1,X3)) = k9_relat_1(sK1,k4_xboole_0(X2,X3))) )),
% 1.45/0.54    inference(superposition,[],[f80,f66])).
% 1.45/0.54  fof(f66,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f10])).
% 1.45/0.54  fof(f10,axiom,(
% 1.45/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.45/0.54  fof(f80,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k4_xboole_0(X0,X1))) )),
% 1.45/0.54    inference(forward_demodulation,[],[f79,f66])).
% 1.45/0.54  fof(f79,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f78,f44])).
% 1.45/0.54  fof(f78,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f77,f45])).
% 1.45/0.54  fof(f77,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.45/0.54    inference(resolution,[],[f46,f63])).
% 1.45/0.54  fof(f63,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f35])).
% 1.45/0.54  fof(f35,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.45/0.54    inference(flattening,[],[f34])).
% 1.45/0.54  % (1749)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.45/0.54  fof(f34,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.45/0.54    inference(ennf_transformation,[],[f15])).
% 1.45/0.54  fof(f15,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 1.45/0.54  fof(f46,plain,(
% 1.45/0.54    v2_funct_1(sK1)),
% 1.45/0.54    inference(cnf_transformation,[],[f40])).
% 1.45/0.54  fof(f64,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f37])).
% 1.45/0.54  fof(f37,plain,(
% 1.45/0.54    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 1.45/0.54    inference(flattening,[],[f36])).
% 1.45/0.54  fof(f36,plain,(
% 1.45/0.54    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f11])).
% 1.45/0.54  fof(f11,axiom,(
% 1.45/0.54    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 1.45/0.54  fof(f51,plain,(
% 1.45/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f41])).
% 1.45/0.54  % SZS output end Proof for theBenchmark
% 1.45/0.54  % (1754)------------------------------
% 1.45/0.54  % (1754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (1754)Termination reason: Refutation
% 1.45/0.54  
% 1.45/0.54  % (1754)Memory used [KB]: 1918
% 1.45/0.54  % (1754)Time elapsed: 0.107 s
% 1.45/0.54  % (1754)------------------------------
% 1.45/0.54  % (1754)------------------------------
% 1.45/0.55  % (1739)Success in time 0.193 s
%------------------------------------------------------------------------------
