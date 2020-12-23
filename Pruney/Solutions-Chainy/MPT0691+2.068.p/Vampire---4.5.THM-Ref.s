%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:54 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 111 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :  111 ( 288 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f299])).

fof(f299,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f292,f48])).

fof(f48,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f292,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_3 ),
    inference(superposition,[],[f190,f290])).

fof(f290,plain,
    ( sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f123,f74])).

fof(f74,plain,(
    ! [X4] : k2_relat_1(k7_relat_1(sK1,X4)) = k9_relat_1(sK1,X4) ),
    inference(resolution,[],[f46,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f123,plain,
    ( sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f119,f80])).

fof(f80,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f77,f46])).

fof(f77,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f47,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f47,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f119,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f98,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f98,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_3
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f190,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),X0),k10_relat_1(sK1,X0))
    | ~ spl2_3 ),
    inference(superposition,[],[f185,f71])).

fof(f71,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f46,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f185,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),X0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f180,f98])).

fof(f180,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(sK0,X0),X0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0)) )
    | ~ spl2_3 ),
    inference(superposition,[],[f54,f122])).

fof(f122,plain,
    ( ! [X3] : k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X3)) = k3_xboole_0(sK0,X3)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f117,f80])).

% (20104)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f117,plain,
    ( ! [X3] : k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X3) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X3))
    | ~ spl2_3 ),
    inference(resolution,[],[f98,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f114,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f112,f46])).

fof(f112,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_3 ),
    inference(resolution,[],[f99,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f99,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:40:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (20108)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (20109)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (20091)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (20110)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (20101)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.25/0.53  % (20103)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.25/0.53  % (20089)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.25/0.53  % (20100)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.25/0.53  % (20102)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.25/0.53  % (20094)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.25/0.54  % (20092)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.25/0.54  % (20107)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.25/0.54  % (20088)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.54  % (20093)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.46/0.55  % (20087)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.46/0.55  % (20106)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.46/0.55  % (20098)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.46/0.55  % (20111)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.46/0.55  % (20105)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.46/0.56  % (20097)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.46/0.56  % (20095)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.46/0.56  % (20099)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.46/0.56  % (20112)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.46/0.57  % (20113)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.46/0.57  % (20096)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.46/0.57  % (20088)Refutation found. Thanks to Tanya!
% 1.46/0.57  % SZS status Theorem for theBenchmark
% 1.46/0.57  % SZS output start Proof for theBenchmark
% 1.46/0.57  fof(f305,plain,(
% 1.46/0.57    $false),
% 1.46/0.57    inference(avatar_sat_refutation,[],[f114,f299])).
% 1.46/0.57  fof(f299,plain,(
% 1.46/0.57    ~spl2_3),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f298])).
% 1.46/0.57  fof(f298,plain,(
% 1.46/0.57    $false | ~spl2_3),
% 1.46/0.57    inference(subsumption_resolution,[],[f292,f48])).
% 1.46/0.57  fof(f48,plain,(
% 1.46/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.46/0.57    inference(cnf_transformation,[],[f43])).
% 1.46/0.57  fof(f43,plain,(
% 1.46/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f42])).
% 1.46/0.57  fof(f42,plain,(
% 1.46/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f22,plain,(
% 1.46/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.46/0.57    inference(flattening,[],[f21])).
% 1.46/0.57  fof(f21,plain,(
% 1.46/0.57    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f20])).
% 1.46/0.57  fof(f20,negated_conjecture,(
% 1.46/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.46/0.57    inference(negated_conjecture,[],[f19])).
% 1.46/0.57  fof(f19,conjecture,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.46/0.57  fof(f292,plain,(
% 1.46/0.57    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_3),
% 1.46/0.57    inference(superposition,[],[f190,f290])).
% 1.46/0.57  fof(f290,plain,(
% 1.46/0.57    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~spl2_3),
% 1.46/0.57    inference(forward_demodulation,[],[f123,f74])).
% 1.46/0.57  fof(f74,plain,(
% 1.46/0.57    ( ! [X4] : (k2_relat_1(k7_relat_1(sK1,X4)) = k9_relat_1(sK1,X4)) )),
% 1.46/0.57    inference(resolution,[],[f46,f55])).
% 1.46/0.57  fof(f55,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f28])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f8])).
% 1.46/0.57  fof(f8,axiom,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.46/0.57  fof(f46,plain,(
% 1.46/0.57    v1_relat_1(sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f43])).
% 1.46/0.57  fof(f123,plain,(
% 1.46/0.57    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) | ~spl2_3),
% 1.46/0.57    inference(forward_demodulation,[],[f119,f80])).
% 1.46/0.57  fof(f80,plain,(
% 1.46/0.57    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.46/0.57    inference(subsumption_resolution,[],[f77,f46])).
% 1.46/0.57  fof(f77,plain,(
% 1.46/0.57    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.46/0.57    inference(resolution,[],[f47,f59])).
% 1.46/0.57  fof(f59,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f33])).
% 1.46/0.57  fof(f33,plain,(
% 1.46/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(flattening,[],[f32])).
% 1.46/0.57  fof(f32,plain,(
% 1.46/0.57    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f15])).
% 1.46/0.57  fof(f15,axiom,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.46/0.57  fof(f47,plain,(
% 1.46/0.57    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.46/0.57    inference(cnf_transformation,[],[f43])).
% 1.46/0.57  fof(f119,plain,(
% 1.46/0.57    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) | ~spl2_3),
% 1.46/0.57    inference(resolution,[],[f98,f50])).
% 1.46/0.57  fof(f50,plain,(
% 1.46/0.57    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f24])).
% 1.46/0.57  fof(f24,plain,(
% 1.46/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.57    inference(ennf_transformation,[],[f10])).
% 1.46/0.57  fof(f10,axiom,(
% 1.46/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.46/0.57  fof(f98,plain,(
% 1.46/0.57    v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_3),
% 1.46/0.57    inference(avatar_component_clause,[],[f97])).
% 1.46/0.57  fof(f97,plain,(
% 1.46/0.57    spl2_3 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.46/0.57  fof(f190,plain,(
% 1.46/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),X0),k10_relat_1(sK1,X0))) ) | ~spl2_3),
% 1.46/0.57    inference(superposition,[],[f185,f71])).
% 1.46/0.57  fof(f71,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 1.46/0.57    inference(resolution,[],[f46,f65])).
% 1.46/0.57  fof(f65,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f37])).
% 1.46/0.57  fof(f37,plain,(
% 1.46/0.57    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.46/0.57    inference(ennf_transformation,[],[f18])).
% 1.46/0.57  fof(f18,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.46/0.57  fof(f185,plain,(
% 1.46/0.57    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),X0)) ) | ~spl2_3),
% 1.46/0.57    inference(subsumption_resolution,[],[f180,f98])).
% 1.46/0.57  fof(f180,plain,(
% 1.46/0.57    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),X0) | ~v1_relat_1(k7_relat_1(sK1,sK0))) ) | ~spl2_3),
% 1.46/0.57    inference(superposition,[],[f54,f122])).
% 1.46/0.57  fof(f122,plain,(
% 1.46/0.57    ( ! [X3] : (k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X3)) = k3_xboole_0(sK0,X3)) ) | ~spl2_3),
% 1.46/0.57    inference(forward_demodulation,[],[f117,f80])).
% 1.46/0.57  % (20104)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.46/0.57  fof(f117,plain,(
% 1.46/0.57    ( ! [X3] : (k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X3) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X3))) ) | ~spl2_3),
% 1.46/0.57    inference(resolution,[],[f98,f57])).
% 1.46/0.57  fof(f57,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f30])).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f14])).
% 1.46/0.57  fof(f14,axiom,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.46/0.57  fof(f54,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f27])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f13])).
% 1.46/0.57  fof(f13,axiom,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.46/0.57  fof(f114,plain,(
% 1.46/0.57    spl2_3),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f113])).
% 1.46/0.57  fof(f113,plain,(
% 1.46/0.57    $false | spl2_3),
% 1.46/0.57    inference(subsumption_resolution,[],[f112,f46])).
% 1.46/0.57  fof(f112,plain,(
% 1.46/0.57    ~v1_relat_1(sK1) | spl2_3),
% 1.46/0.57    inference(resolution,[],[f99,f52])).
% 1.46/0.57  fof(f52,plain,(
% 1.46/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f25])).
% 1.46/0.57  fof(f25,plain,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.46/0.57    inference(ennf_transformation,[],[f7])).
% 1.46/0.57  fof(f7,axiom,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.46/0.57  fof(f99,plain,(
% 1.46/0.57    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_3),
% 1.46/0.57    inference(avatar_component_clause,[],[f97])).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (20088)------------------------------
% 1.46/0.57  % (20088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (20088)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (20088)Memory used [KB]: 10746
% 1.46/0.57  % (20088)Time elapsed: 0.126 s
% 1.46/0.57  % (20088)------------------------------
% 1.46/0.57  % (20088)------------------------------
% 1.46/0.57  % (20085)Success in time 0.207 s
%------------------------------------------------------------------------------
