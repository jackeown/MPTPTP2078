%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:49 EST 2020

% Result     : Theorem 2.24s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 115 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 259 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f77,f93,f803,f1179])).

fof(f1179,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f1178])).

fof(f1178,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f1134,f802])).

fof(f802,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f800])).

fof(f800,plain,
    ( spl2_11
  <=> r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f1134,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f303,f378])).

fof(f378,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1)))
    | ~ spl2_3 ),
    inference(superposition,[],[f125,f65])).

fof(f65,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f62,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f125,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f118,f68])).

fof(f68,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f62,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f118,plain,
    ( ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f64,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f64,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f62,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f303,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))
    | spl2_1 ),
    inference(superposition,[],[f109,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f109,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0))
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f46,f52,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f52,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f803,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f793,f89,f73,f60,f800])).

fof(f73,plain,
    ( spl2_4
  <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f89,plain,
    ( spl2_5
  <=> sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f793,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f316,f91])).

fof(f91,plain,
    ( sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f316,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f124,f75])).

fof(f75,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f124,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f119,f65])).

fof(f119,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f64,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f93,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f85,f55,f89])).

fof(f55,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f57,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f77,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f70,f60,f73])).

fof(f70,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f62,f42])).

fof(f63,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f58,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f33,f50])).

fof(f33,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (31477)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (31480)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (31486)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.56  % (31500)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.56  % (31475)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (31481)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (31479)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.56  % (31495)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (31493)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.57  % (31497)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.57  % (31489)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.58  % (31498)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.58  % (31488)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.58  % (31490)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.58  % (31492)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.59  % (31487)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.59  % (31482)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.59  % (31476)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.85/0.60  % (31485)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.85/0.60  % (31483)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 2.01/0.62  % (31478)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 2.01/0.63  % (31494)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 2.01/0.64  % (31499)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.01/0.64  % (31484)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 2.24/0.65  % (31491)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.24/0.65  % (31496)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 2.24/0.66  % (31488)Refutation found. Thanks to Tanya!
% 2.24/0.66  % SZS status Theorem for theBenchmark
% 2.24/0.67  % SZS output start Proof for theBenchmark
% 2.24/0.67  fof(f1180,plain,(
% 2.24/0.67    $false),
% 2.24/0.67    inference(avatar_sat_refutation,[],[f53,f58,f63,f77,f93,f803,f1179])).
% 2.24/0.67  fof(f1179,plain,(
% 2.24/0.67    spl2_1 | ~spl2_3 | ~spl2_11),
% 2.24/0.67    inference(avatar_contradiction_clause,[],[f1178])).
% 2.24/0.67  fof(f1178,plain,(
% 2.24/0.67    $false | (spl2_1 | ~spl2_3 | ~spl2_11)),
% 2.24/0.67    inference(subsumption_resolution,[],[f1134,f802])).
% 2.24/0.67  fof(f802,plain,(
% 2.24/0.67    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~spl2_11),
% 2.24/0.67    inference(avatar_component_clause,[],[f800])).
% 2.24/0.67  fof(f800,plain,(
% 2.24/0.67    spl2_11 <=> r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 2.24/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.24/0.67  fof(f1134,plain,(
% 2.24/0.67    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | (spl2_1 | ~spl2_3)),
% 2.24/0.67    inference(superposition,[],[f303,f378])).
% 2.24/0.67  fof(f378,plain,(
% 2.24/0.67    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1)))) ) | ~spl2_3),
% 2.24/0.67    inference(superposition,[],[f125,f65])).
% 2.24/0.67  fof(f65,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) ) | ~spl2_3),
% 2.24/0.67    inference(unit_resulting_resolution,[],[f62,f43])).
% 2.24/0.67  fof(f43,plain,(
% 2.24/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 2.24/0.67    inference(cnf_transformation,[],[f24])).
% 2.24/0.67  fof(f24,plain,(
% 2.24/0.67    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.24/0.67    inference(ennf_transformation,[],[f13])).
% 2.24/0.67  fof(f13,axiom,(
% 2.24/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.24/0.67  fof(f62,plain,(
% 2.24/0.67    v1_relat_1(sK1) | ~spl2_3),
% 2.24/0.67    inference(avatar_component_clause,[],[f60])).
% 2.24/0.67  fof(f60,plain,(
% 2.24/0.67    spl2_3 <=> v1_relat_1(sK1)),
% 2.24/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.24/0.67  fof(f125,plain,(
% 2.24/0.67    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) ) | ~spl2_3),
% 2.24/0.67    inference(forward_demodulation,[],[f118,f68])).
% 2.24/0.67  fof(f68,plain,(
% 2.24/0.67    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_3),
% 2.24/0.67    inference(unit_resulting_resolution,[],[f62,f34])).
% 2.24/0.67  fof(f34,plain,(
% 2.24/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f18])).
% 2.24/0.67  fof(f18,plain,(
% 2.24/0.67    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.24/0.67    inference(ennf_transformation,[],[f10])).
% 2.24/0.67  fof(f10,axiom,(
% 2.24/0.67    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.24/0.67  fof(f118,plain,(
% 2.24/0.67    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_3),
% 2.24/0.67    inference(unit_resulting_resolution,[],[f64,f42])).
% 2.24/0.67  fof(f42,plain,(
% 2.24/0.67    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f23])).
% 2.24/0.67  fof(f23,plain,(
% 2.24/0.67    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.24/0.67    inference(ennf_transformation,[],[f12])).
% 2.24/0.67  fof(f12,axiom,(
% 2.24/0.67    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.24/0.67  fof(f64,plain,(
% 2.24/0.67    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_3),
% 2.24/0.67    inference(unit_resulting_resolution,[],[f62,f44])).
% 2.24/0.67  fof(f44,plain,(
% 2.24/0.67    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f25])).
% 2.24/0.67  fof(f25,plain,(
% 2.24/0.67    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.24/0.67    inference(ennf_transformation,[],[f9])).
% 2.24/0.67  fof(f9,axiom,(
% 2.24/0.67    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.24/0.67  fof(f303,plain,(
% 2.24/0.67    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ) | spl2_1),
% 2.24/0.67    inference(superposition,[],[f109,f41])).
% 2.24/0.67  fof(f41,plain,(
% 2.24/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f1])).
% 2.24/0.67  fof(f1,axiom,(
% 2.24/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.24/0.67  fof(f109,plain,(
% 2.24/0.67    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0))) ) | spl2_1),
% 2.24/0.67    inference(unit_resulting_resolution,[],[f46,f52,f35])).
% 2.24/0.67  fof(f35,plain,(
% 2.24/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f20])).
% 2.24/0.67  fof(f20,plain,(
% 2.24/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.24/0.67    inference(flattening,[],[f19])).
% 2.24/0.67  fof(f19,plain,(
% 2.24/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.24/0.67    inference(ennf_transformation,[],[f6])).
% 2.24/0.67  fof(f6,axiom,(
% 2.24/0.67    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.24/0.67  fof(f52,plain,(
% 2.24/0.67    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | spl2_1),
% 2.24/0.67    inference(avatar_component_clause,[],[f50])).
% 2.24/0.67  fof(f50,plain,(
% 2.24/0.67    spl2_1 <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.24/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.24/0.67  fof(f46,plain,(
% 2.24/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f5])).
% 2.24/0.67  fof(f5,axiom,(
% 2.24/0.67    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.24/0.67  fof(f803,plain,(
% 2.24/0.67    spl2_11 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 2.24/0.67    inference(avatar_split_clause,[],[f793,f89,f73,f60,f800])).
% 2.24/0.67  fof(f73,plain,(
% 2.24/0.67    spl2_4 <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 2.24/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.24/0.67  fof(f89,plain,(
% 2.24/0.67    spl2_5 <=> sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 2.24/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.24/0.67  fof(f793,plain,(
% 2.24/0.67    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 2.24/0.67    inference(superposition,[],[f316,f91])).
% 2.24/0.67  fof(f91,plain,(
% 2.24/0.67    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_5),
% 2.24/0.67    inference(avatar_component_clause,[],[f89])).
% 2.24/0.67  fof(f316,plain,(
% 2.24/0.67    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0)))) ) | (~spl2_3 | ~spl2_4)),
% 2.24/0.67    inference(superposition,[],[f124,f75])).
% 2.24/0.67  fof(f75,plain,(
% 2.24/0.67    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl2_4),
% 2.24/0.67    inference(avatar_component_clause,[],[f73])).
% 2.24/0.67  fof(f124,plain,(
% 2.24/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_3),
% 2.24/0.67    inference(forward_demodulation,[],[f119,f65])).
% 2.24/0.67  fof(f119,plain,(
% 2.24/0.67    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_3),
% 2.24/0.67    inference(unit_resulting_resolution,[],[f64,f36])).
% 2.24/0.67  fof(f36,plain,(
% 2.24/0.67    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.24/0.67    inference(cnf_transformation,[],[f21])).
% 2.24/0.67  fof(f21,plain,(
% 2.24/0.67    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.24/0.67    inference(ennf_transformation,[],[f11])).
% 2.24/0.67  fof(f11,axiom,(
% 2.24/0.67    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.24/0.67  fof(f93,plain,(
% 2.24/0.67    spl2_5 | ~spl2_2),
% 2.24/0.67    inference(avatar_split_clause,[],[f85,f55,f89])).
% 2.24/0.67  fof(f55,plain,(
% 2.24/0.67    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 2.24/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.24/0.67  fof(f85,plain,(
% 2.24/0.67    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 2.24/0.67    inference(resolution,[],[f57,f40])).
% 2.24/0.67  fof(f40,plain,(
% 2.24/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.24/0.67    inference(cnf_transformation,[],[f22])).
% 2.24/0.67  fof(f22,plain,(
% 2.24/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.24/0.67    inference(ennf_transformation,[],[f7])).
% 2.24/0.67  fof(f7,axiom,(
% 2.24/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.24/0.67  fof(f57,plain,(
% 2.24/0.67    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 2.24/0.67    inference(avatar_component_clause,[],[f55])).
% 2.24/0.67  fof(f77,plain,(
% 2.24/0.67    spl2_4 | ~spl2_3),
% 2.24/0.67    inference(avatar_split_clause,[],[f70,f60,f73])).
% 2.24/0.67  fof(f70,plain,(
% 2.24/0.67    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl2_3),
% 2.24/0.67    inference(resolution,[],[f62,f42])).
% 2.24/0.67  fof(f63,plain,(
% 2.24/0.67    spl2_3),
% 2.24/0.67    inference(avatar_split_clause,[],[f31,f60])).
% 2.24/0.67  fof(f31,plain,(
% 2.24/0.67    v1_relat_1(sK1)),
% 2.24/0.67    inference(cnf_transformation,[],[f28])).
% 2.24/0.67  fof(f28,plain,(
% 2.24/0.67    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 2.24/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).
% 2.24/0.67  fof(f27,plain,(
% 2.24/0.67    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 2.24/0.67    introduced(choice_axiom,[])).
% 2.24/0.67  fof(f17,plain,(
% 2.24/0.67    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.24/0.67    inference(flattening,[],[f16])).
% 2.24/0.67  fof(f16,plain,(
% 2.24/0.67    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.24/0.67    inference(ennf_transformation,[],[f15])).
% 2.24/0.67  fof(f15,negated_conjecture,(
% 2.24/0.67    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.24/0.67    inference(negated_conjecture,[],[f14])).
% 2.24/0.67  fof(f14,conjecture,(
% 2.24/0.67    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.24/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.24/0.67  fof(f58,plain,(
% 2.24/0.67    spl2_2),
% 2.24/0.67    inference(avatar_split_clause,[],[f32,f55])).
% 2.24/0.67  fof(f32,plain,(
% 2.24/0.67    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.24/0.67    inference(cnf_transformation,[],[f28])).
% 2.24/0.67  fof(f53,plain,(
% 2.24/0.67    ~spl2_1),
% 2.24/0.67    inference(avatar_split_clause,[],[f33,f50])).
% 2.24/0.67  fof(f33,plain,(
% 2.24/0.67    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.24/0.67    inference(cnf_transformation,[],[f28])).
% 2.24/0.67  % SZS output end Proof for theBenchmark
% 2.24/0.67  % (31488)------------------------------
% 2.24/0.67  % (31488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.67  % (31488)Termination reason: Refutation
% 2.24/0.67  
% 2.24/0.67  % (31488)Memory used [KB]: 6780
% 2.24/0.67  % (31488)Time elapsed: 0.223 s
% 2.24/0.67  % (31488)------------------------------
% 2.24/0.67  % (31488)------------------------------
% 2.24/0.67  % (31474)Success in time 0.308 s
%------------------------------------------------------------------------------
