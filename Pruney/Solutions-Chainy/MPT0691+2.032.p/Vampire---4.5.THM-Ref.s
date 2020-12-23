%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:49 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 103 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  109 ( 258 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2068,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2067,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2067,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f2066,f96])).

fof(f96,plain,(
    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f46,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f2066,plain,(
    ~ r1_tarski(sK0,k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f2000,f143])).

fof(f143,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f2000,plain,(
    ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f255,f1980,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1980,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ),
    inference(forward_demodulation,[],[f1979,f172])).

fof(f172,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f45,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f1979,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ),
    inference(forward_demodulation,[],[f1978,f146])).

fof(f146,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1978,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k3_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X0))))) ),
    inference(forward_demodulation,[],[f151,f172])).

fof(f151,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f69,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f45,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f255,plain,(
    ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) ),
    inference(superposition,[],[f110,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f110,plain,(
    ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)) ),
    inference(unit_resulting_resolution,[],[f47,f62,f52])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f47,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (25983)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (25990)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (25984)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (25974)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.23/0.52  % (25982)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.23/0.52  % (25992)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.23/0.52  % (25973)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.23/0.52  % (25987)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.23/0.52  % (25993)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.23/0.52  % (25976)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.23/0.52  % (25981)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.23/0.52  % (25985)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.23/0.52  % (25979)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.23/0.53  % (25977)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.23/0.53  % (25975)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.23/0.53  % (25995)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.23/0.53  % (25994)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.23/0.53  % (25991)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.23/0.53  % (25988)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.23/0.53  % (25978)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.23/0.53  % (25972)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.53  % (25996)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.44/0.54  % (25980)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.44/0.54  % (25986)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.44/0.54  % (25971)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.44/0.55  % (25989)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 2.12/0.66  % (25971)Refutation found. Thanks to Tanya!
% 2.12/0.66  % SZS status Theorem for theBenchmark
% 2.12/0.67  % SZS output start Proof for theBenchmark
% 2.12/0.67  fof(f2068,plain,(
% 2.12/0.67    $false),
% 2.12/0.67    inference(subsumption_resolution,[],[f2067,f67])).
% 2.12/0.67  fof(f67,plain,(
% 2.12/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.12/0.67    inference(equality_resolution,[],[f57])).
% 2.12/0.67  fof(f57,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.12/0.67    inference(cnf_transformation,[],[f44])).
% 2.12/0.67  fof(f44,plain,(
% 2.12/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.67    inference(flattening,[],[f43])).
% 2.12/0.67  fof(f43,plain,(
% 2.12/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.12/0.67    inference(nnf_transformation,[],[f2])).
% 2.12/0.67  fof(f2,axiom,(
% 2.12/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.12/0.67  fof(f2067,plain,(
% 2.12/0.67    ~r1_tarski(sK0,sK0)),
% 2.12/0.67    inference(forward_demodulation,[],[f2066,f96])).
% 2.12/0.67  fof(f96,plain,(
% 2.12/0.67    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 2.12/0.67    inference(unit_resulting_resolution,[],[f46,f60])).
% 2.12/0.67  fof(f60,plain,(
% 2.12/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.12/0.67    inference(cnf_transformation,[],[f36])).
% 2.12/0.67  fof(f36,plain,(
% 2.12/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.12/0.67    inference(ennf_transformation,[],[f6])).
% 2.12/0.67  fof(f6,axiom,(
% 2.12/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.12/0.67  fof(f46,plain,(
% 2.12/0.67    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.12/0.67    inference(cnf_transformation,[],[f42])).
% 2.12/0.67  fof(f42,plain,(
% 2.12/0.67    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 2.12/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f41])).
% 2.12/0.67  fof(f41,plain,(
% 2.12/0.67    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 2.12/0.67    introduced(choice_axiom,[])).
% 2.12/0.67  fof(f23,plain,(
% 2.12/0.67    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.12/0.67    inference(flattening,[],[f22])).
% 2.12/0.67  fof(f22,plain,(
% 2.12/0.67    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.12/0.67    inference(ennf_transformation,[],[f21])).
% 2.12/0.67  fof(f21,negated_conjecture,(
% 2.12/0.67    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.12/0.67    inference(negated_conjecture,[],[f20])).
% 2.12/0.67  fof(f20,conjecture,(
% 2.12/0.67    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.12/0.67  fof(f2066,plain,(
% 2.12/0.67    ~r1_tarski(sK0,k3_xboole_0(sK0,k1_relat_1(sK1)))),
% 2.12/0.67    inference(superposition,[],[f2000,f143])).
% 2.12/0.67  fof(f143,plain,(
% 2.12/0.67    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 2.12/0.67    inference(unit_resulting_resolution,[],[f45,f66])).
% 2.12/0.67  fof(f66,plain,(
% 2.12/0.67    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f40])).
% 2.12/0.67  fof(f40,plain,(
% 2.12/0.67    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.12/0.67    inference(ennf_transformation,[],[f13])).
% 2.12/0.67  fof(f13,axiom,(
% 2.12/0.67    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.12/0.67  fof(f45,plain,(
% 2.12/0.67    v1_relat_1(sK1)),
% 2.12/0.67    inference(cnf_transformation,[],[f42])).
% 2.12/0.67  fof(f2000,plain,(
% 2.12/0.67    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X0)))) )),
% 2.12/0.67    inference(unit_resulting_resolution,[],[f255,f1980,f52])).
% 2.12/0.67  fof(f52,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f29])).
% 2.12/0.67  fof(f29,plain,(
% 2.12/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.12/0.67    inference(flattening,[],[f28])).
% 2.12/0.67  fof(f28,plain,(
% 2.12/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.12/0.67    inference(ennf_transformation,[],[f5])).
% 2.12/0.67  fof(f5,axiom,(
% 2.12/0.67    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.12/0.67  fof(f1980,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))) )),
% 2.12/0.67    inference(forward_demodulation,[],[f1979,f172])).
% 2.12/0.67  fof(f172,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 2.12/0.67    inference(unit_resulting_resolution,[],[f45,f48])).
% 2.12/0.67  fof(f48,plain,(
% 2.12/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f24])).
% 2.12/0.67  fof(f24,plain,(
% 2.12/0.67    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.12/0.67    inference(ennf_transformation,[],[f19])).
% 2.12/0.67  fof(f19,axiom,(
% 2.12/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.12/0.67  fof(f1979,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))) )),
% 2.12/0.67    inference(forward_demodulation,[],[f1978,f146])).
% 2.12/0.67  fof(f146,plain,(
% 2.12/0.67    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 2.12/0.67    inference(unit_resulting_resolution,[],[f45,f50])).
% 2.12/0.67  fof(f50,plain,(
% 2.12/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f26])).
% 2.12/0.67  fof(f26,plain,(
% 2.12/0.67    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.12/0.67    inference(ennf_transformation,[],[f10])).
% 2.12/0.67  fof(f10,axiom,(
% 2.12/0.67    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.12/0.67  fof(f1978,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k3_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X0)))))) )),
% 2.12/0.67    inference(forward_demodulation,[],[f151,f172])).
% 2.12/0.67  fof(f151,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))))) )),
% 2.12/0.67    inference(unit_resulting_resolution,[],[f69,f65])).
% 2.12/0.67  fof(f65,plain,(
% 2.12/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 2.12/0.67    inference(cnf_transformation,[],[f39])).
% 2.12/0.67  fof(f39,plain,(
% 2.12/0.67    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.12/0.67    inference(ennf_transformation,[],[f14])).
% 2.12/0.67  fof(f14,axiom,(
% 2.12/0.67    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 2.12/0.67  fof(f69,plain,(
% 2.12/0.67    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 2.12/0.67    inference(unit_resulting_resolution,[],[f45,f64])).
% 2.12/0.67  fof(f64,plain,(
% 2.12/0.67    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f38])).
% 2.12/0.67  fof(f38,plain,(
% 2.12/0.67    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.12/0.67    inference(ennf_transformation,[],[f9])).
% 2.12/0.67  fof(f9,axiom,(
% 2.12/0.67    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.12/0.67  fof(f255,plain,(
% 2.12/0.67    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) )),
% 2.12/0.67    inference(superposition,[],[f110,f61])).
% 2.12/0.67  fof(f61,plain,(
% 2.12/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f1])).
% 2.12/0.67  fof(f1,axiom,(
% 2.12/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.12/0.67  fof(f110,plain,(
% 2.12/0.67    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0))) )),
% 2.12/0.67    inference(unit_resulting_resolution,[],[f47,f62,f52])).
% 2.12/0.67  fof(f62,plain,(
% 2.12/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f4])).
% 2.12/0.67  fof(f4,axiom,(
% 2.12/0.67    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.12/0.67  fof(f47,plain,(
% 2.12/0.67    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.12/0.67    inference(cnf_transformation,[],[f42])).
% 2.12/0.67  % SZS output end Proof for theBenchmark
% 2.12/0.67  % (25971)------------------------------
% 2.12/0.67  % (25971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.67  % (25971)Termination reason: Refutation
% 2.12/0.67  
% 2.12/0.67  % (25971)Memory used [KB]: 12665
% 2.12/0.67  % (25971)Time elapsed: 0.253 s
% 2.12/0.67  % (25971)------------------------------
% 2.12/0.67  % (25971)------------------------------
% 2.12/0.68  % (25970)Success in time 0.325 s
%------------------------------------------------------------------------------
