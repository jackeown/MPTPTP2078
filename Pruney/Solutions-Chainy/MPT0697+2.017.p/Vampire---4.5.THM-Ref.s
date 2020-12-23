%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:08 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
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
fof(f371,plain,(
    $false ),
    inference(resolution,[],[f356,f41])).

fof(f41,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33])).

fof(f33,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f356,plain,(
    ! [X4] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4) ),
    inference(trivial_inequality_removal,[],[f354])).

fof(f354,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4) ) ),
    inference(superposition,[],[f43,f343])).

fof(f343,plain,(
    ! [X12] : k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12) ),
    inference(subsumption_resolution,[],[f342,f38])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f342,plain,(
    ! [X12] :
      ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f330,f120])).

fof(f120,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1)) ),
    inference(resolution,[],[f73,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f73,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,k10_relat_1(sK1,X5))
      | r1_tarski(X4,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f62,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f330,plain,(
    ! [X12] :
      ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12),k1_relat_1(sK1))
      | k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)
      | ~ v1_relat_1(sK1) ) ),
    inference(trivial_inequality_removal,[],[f329])).

fof(f329,plain,(
    ! [X12] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12),k1_relat_1(sK1))
      | k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f49,f168])).

fof(f168,plain,(
    ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2)) ),
    inference(superposition,[],[f90,f77])).

fof(f77,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2) ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f64,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f63,f38])).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ! [X2,X3] : k4_xboole_0(k9_relat_1(sK1,X2),k9_relat_1(sK1,X3)) = k9_relat_1(sK1,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f68,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f68,plain,(
    ! [X0,X1] : k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f67,f57])).

fof(f67,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f66,f38])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f65,f39])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f40,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f40,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (10338)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (10346)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (10354)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (10351)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (10334)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (10350)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (10335)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (10343)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.57/0.57  % (10345)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.57/0.58  % (10347)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.57/0.58  % (10328)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.57/0.58  % (10344)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.57/0.58  % (10342)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.58  % (10337)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.57/0.58  % (10342)Refutation not found, incomplete strategy% (10342)------------------------------
% 1.57/0.58  % (10342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (10330)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.57/0.58  % (10333)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.58  % (10336)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.71/0.58  % (10353)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.71/0.58  % (10329)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.71/0.58  % (10342)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.58  
% 1.71/0.58  % (10342)Memory used [KB]: 10618
% 1.71/0.58  % (10342)Time elapsed: 0.149 s
% 1.71/0.58  % (10342)------------------------------
% 1.71/0.58  % (10342)------------------------------
% 1.71/0.58  % (10349)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.71/0.59  % (10348)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.71/0.59  % (10339)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.71/0.59  % (10355)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.71/0.59  % (10332)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.71/0.59  % (10326)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.71/0.60  % (10352)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.71/0.60  % (10327)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.71/0.60  % (10341)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.71/0.61  % (10331)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.71/0.61  % (10340)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.97/0.63  % (10340)Refutation found. Thanks to Tanya!
% 1.97/0.63  % SZS status Theorem for theBenchmark
% 1.97/0.63  % SZS output start Proof for theBenchmark
% 1.97/0.63  fof(f371,plain,(
% 1.97/0.63    $false),
% 1.97/0.63    inference(resolution,[],[f356,f41])).
% 1.97/0.63  fof(f41,plain,(
% 1.97/0.63    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.97/0.63    inference(cnf_transformation,[],[f34])).
% 1.97/0.63  fof(f34,plain,(
% 1.97/0.63    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.97/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33])).
% 1.97/0.63  fof(f33,plain,(
% 1.97/0.63    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f18,plain,(
% 1.97/0.63    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.97/0.63    inference(flattening,[],[f17])).
% 1.97/0.63  fof(f17,plain,(
% 1.97/0.63    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.97/0.63    inference(ennf_transformation,[],[f16])).
% 1.97/0.63  fof(f16,negated_conjecture,(
% 1.97/0.63    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.97/0.63    inference(negated_conjecture,[],[f15])).
% 1.97/0.63  fof(f15,conjecture,(
% 1.97/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.97/0.63  fof(f356,plain,(
% 1.97/0.63    ( ! [X4] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)) )),
% 1.97/0.63    inference(trivial_inequality_removal,[],[f354])).
% 1.97/0.63  fof(f354,plain,(
% 1.97/0.63    ( ! [X4] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)) )),
% 1.97/0.63    inference(superposition,[],[f43,f343])).
% 1.97/0.63  fof(f343,plain,(
% 1.97/0.63    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12)) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f342,f38])).
% 1.97/0.63  fof(f38,plain,(
% 1.97/0.63    v1_relat_1(sK1)),
% 1.97/0.63    inference(cnf_transformation,[],[f34])).
% 1.97/0.63  fof(f342,plain,(
% 1.97/0.63    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12) | ~v1_relat_1(sK1)) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f330,f120])).
% 1.97/0.63  fof(f120,plain,(
% 1.97/0.63    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))) )),
% 1.97/0.63    inference(resolution,[],[f73,f52])).
% 1.97/0.63  fof(f52,plain,(
% 1.97/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f5])).
% 1.97/0.63  fof(f5,axiom,(
% 1.97/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.97/0.63  fof(f73,plain,(
% 1.97/0.63    ( ! [X4,X5] : (~r1_tarski(X4,k10_relat_1(sK1,X5)) | r1_tarski(X4,k1_relat_1(sK1))) )),
% 1.97/0.63    inference(resolution,[],[f62,f42])).
% 1.97/0.63  fof(f42,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f20])).
% 1.97/0.63  fof(f20,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.97/0.63    inference(flattening,[],[f19])).
% 1.97/0.63  fof(f19,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.97/0.63    inference(ennf_transformation,[],[f4])).
% 1.97/0.63  fof(f4,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.97/0.63  fof(f62,plain,(
% 1.97/0.63    ( ! [X2] : (r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))) )),
% 1.97/0.63    inference(resolution,[],[f38,f51])).
% 1.97/0.63  fof(f51,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f27])).
% 1.97/0.63  fof(f27,plain,(
% 1.97/0.63    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(ennf_transformation,[],[f10])).
% 1.97/0.63  fof(f10,axiom,(
% 1.97/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.97/0.63  fof(f330,plain,(
% 1.97/0.63    ( ! [X12] : (~r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12),k1_relat_1(sK1)) | k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12) | ~v1_relat_1(sK1)) )),
% 1.97/0.63    inference(trivial_inequality_removal,[],[f329])).
% 1.97/0.63  fof(f329,plain,(
% 1.97/0.63    ( ! [X12] : (k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12),k1_relat_1(sK1)) | k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X12)),X12) | ~v1_relat_1(sK1)) )),
% 1.97/0.63    inference(superposition,[],[f49,f168])).
% 1.97/0.63  fof(f168,plain,(
% 1.97/0.63    ( ! [X2] : (k1_xboole_0 = k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))) )),
% 1.97/0.63    inference(superposition,[],[f90,f77])).
% 1.97/0.63  fof(f77,plain,(
% 1.97/0.63    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2)) )),
% 1.97/0.63    inference(resolution,[],[f64,f44])).
% 1.97/0.63  fof(f44,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.97/0.63    inference(cnf_transformation,[],[f35])).
% 1.97/0.63  fof(f35,plain,(
% 1.97/0.63    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.97/0.63    inference(nnf_transformation,[],[f2])).
% 1.97/0.63  fof(f2,axiom,(
% 1.97/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.97/0.63  fof(f64,plain,(
% 1.97/0.63    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f63,f38])).
% 1.97/0.63  fof(f63,plain,(
% 1.97/0.63    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) )),
% 1.97/0.63    inference(resolution,[],[f39,f48])).
% 1.97/0.63  fof(f48,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f22])).
% 1.97/0.63  fof(f22,plain,(
% 1.97/0.63    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(flattening,[],[f21])).
% 1.97/0.63  fof(f21,plain,(
% 1.97/0.63    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.97/0.63    inference(ennf_transformation,[],[f13])).
% 1.97/0.63  fof(f13,axiom,(
% 1.97/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.97/0.63  fof(f39,plain,(
% 1.97/0.63    v1_funct_1(sK1)),
% 1.97/0.63    inference(cnf_transformation,[],[f34])).
% 1.97/0.63  fof(f90,plain,(
% 1.97/0.63    ( ! [X2,X3] : (k4_xboole_0(k9_relat_1(sK1,X2),k9_relat_1(sK1,X3)) = k9_relat_1(sK1,k4_xboole_0(X2,X3))) )),
% 1.97/0.63    inference(superposition,[],[f68,f57])).
% 1.97/0.63  fof(f57,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f8])).
% 1.97/0.63  fof(f8,axiom,(
% 1.97/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.97/0.63  fof(f68,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k4_xboole_0(X0,X1))) )),
% 1.97/0.63    inference(forward_demodulation,[],[f67,f57])).
% 1.97/0.63  fof(f67,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f66,f38])).
% 1.97/0.63  fof(f66,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f65,f39])).
% 1.97/0.63  fof(f65,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.97/0.63    inference(resolution,[],[f40,f55])).
% 1.97/0.63  fof(f55,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f31])).
% 1.97/0.63  fof(f31,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.97/0.63    inference(flattening,[],[f30])).
% 1.97/0.63  fof(f30,plain,(
% 1.97/0.63    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.97/0.63    inference(ennf_transformation,[],[f12])).
% 1.97/0.63  fof(f12,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.97/0.63  fof(f40,plain,(
% 1.97/0.63    v2_funct_1(sK1)),
% 1.97/0.63    inference(cnf_transformation,[],[f34])).
% 1.97/0.63  fof(f49,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f24])).
% 1.97/0.63  fof(f24,plain,(
% 1.97/0.63    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 1.97/0.63    inference(flattening,[],[f23])).
% 1.97/0.63  fof(f23,plain,(
% 1.97/0.63    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(ennf_transformation,[],[f9])).
% 1.97/0.63  fof(f9,axiom,(
% 1.97/0.63    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 1.97/0.63  fof(f43,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f35])).
% 1.97/0.63  % SZS output end Proof for theBenchmark
% 1.97/0.63  % (10340)------------------------------
% 1.97/0.63  % (10340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (10340)Termination reason: Refutation
% 1.97/0.63  
% 1.97/0.63  % (10340)Memory used [KB]: 1918
% 1.97/0.63  % (10340)Time elapsed: 0.190 s
% 1.97/0.63  % (10340)------------------------------
% 1.97/0.63  % (10340)------------------------------
% 1.97/0.63  % (10325)Success in time 0.267 s
%------------------------------------------------------------------------------
