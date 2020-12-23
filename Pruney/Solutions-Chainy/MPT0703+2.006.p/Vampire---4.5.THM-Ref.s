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
% DateTime   : Thu Dec  3 12:54:19 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 168 expanded)
%              Number of leaves         :    9 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 667 expanded)
%              Number of equality atoms :   18 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(subsumption_resolution,[],[f376,f350])).

fof(f350,plain,(
    ~ r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f97,f318])).

fof(f318,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f57,f54])).

fof(f54,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f57,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f55,f31])).

fof(f55,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ~ r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f58,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f59,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f59,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1) ),
    inference(resolution,[],[f35,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f35,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1) ),
    inference(subsumption_resolution,[],[f56,f31])).

fof(f56,plain,(
    ! [X1] :
      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f376,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f375,f65])).

fof(f65,plain,(
    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f34,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f375,plain,(
    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f374,f318])).

fof(f374,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f373,f318])).

fof(f373,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f75,f31])).

fof(f75,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(sK2,sK0)),k9_relat_1(X1,k10_relat_1(sK2,sK1))) ) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f33,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (19545)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.47  % (19546)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.55  % (19543)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.55  % (19544)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.55  % (19551)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.47/0.56  % (19553)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.47/0.56  % (19542)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.47/0.57  % (19552)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.47/0.57  % (19562)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.47/0.57  % (19548)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.66/0.57  % (19561)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.66/0.57  % (19560)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.66/0.58  % (19558)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.66/0.58  % (19557)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.66/0.59  % (19548)Refutation found. Thanks to Tanya!
% 1.66/0.59  % SZS status Theorem for theBenchmark
% 1.66/0.59  % SZS output start Proof for theBenchmark
% 1.66/0.59  fof(f377,plain,(
% 1.66/0.59    $false),
% 1.66/0.59    inference(subsumption_resolution,[],[f376,f350])).
% 1.66/0.59  fof(f350,plain,(
% 1.66/0.59    ~r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 1.66/0.59    inference(backward_demodulation,[],[f97,f318])).
% 1.66/0.59  fof(f318,plain,(
% 1.66/0.59    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))) )),
% 1.66/0.59    inference(forward_demodulation,[],[f57,f54])).
% 1.66/0.59  fof(f54,plain,(
% 1.66/0.59    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.66/0.59    inference(resolution,[],[f31,f36])).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f16,plain,(
% 1.66/0.59    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.66/0.59    inference(ennf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.66/0.59  fof(f31,plain,(
% 1.66/0.59    v1_relat_1(sK2)),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  fof(f28,plain,(
% 1.66/0.59    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.66/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27])).
% 1.66/0.59  fof(f27,plain,(
% 1.66/0.59    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.66/0.59    introduced(choice_axiom,[])).
% 1.66/0.59  fof(f15,plain,(
% 1.66/0.59    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.66/0.59    inference(flattening,[],[f14])).
% 1.66/0.59  fof(f14,plain,(
% 1.66/0.59    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.66/0.59    inference(ennf_transformation,[],[f13])).
% 1.66/0.59  fof(f13,negated_conjecture,(
% 1.66/0.59    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.66/0.59    inference(negated_conjecture,[],[f12])).
% 1.66/0.59  fof(f12,conjecture,(
% 1.66/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 1.66/0.59  fof(f57,plain,(
% 1.66/0.59    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) )),
% 1.66/0.59    inference(subsumption_resolution,[],[f55,f31])).
% 1.66/0.59  fof(f55,plain,(
% 1.66/0.59    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(sK2)) )),
% 1.66/0.59    inference(resolution,[],[f32,f42])).
% 1.66/0.59  fof(f42,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f22])).
% 1.66/0.59  fof(f22,plain,(
% 1.66/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(flattening,[],[f21])).
% 1.66/0.59  fof(f21,plain,(
% 1.66/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.66/0.59    inference(ennf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,axiom,(
% 1.66/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 1.66/0.59  fof(f32,plain,(
% 1.66/0.59    v1_funct_1(sK2)),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  fof(f97,plain,(
% 1.66/0.59    ~r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 1.66/0.59    inference(resolution,[],[f58,f67])).
% 1.66/0.59  fof(f67,plain,(
% 1.66/0.59    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0)) )),
% 1.66/0.59    inference(superposition,[],[f59,f40])).
% 1.66/0.59  fof(f40,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f4])).
% 1.66/0.59  fof(f4,axiom,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.66/0.59  fof(f59,plain,(
% 1.66/0.59    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK1)) )),
% 1.66/0.59    inference(resolution,[],[f35,f48])).
% 1.66/0.59  fof(f48,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f26])).
% 1.66/0.59  fof(f26,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.66/0.59    inference(ennf_transformation,[],[f3])).
% 1.66/0.59  fof(f3,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    ~r1_tarski(sK0,sK1)),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  fof(f58,plain,(
% 1.66/0.59    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1)) )),
% 1.66/0.59    inference(subsumption_resolution,[],[f56,f31])).
% 1.66/0.59  fof(f56,plain,(
% 1.66/0.59    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X1)),X1) | ~v1_relat_1(sK2)) )),
% 1.66/0.59    inference(resolution,[],[f32,f41])).
% 1.66/0.59  fof(f41,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f20])).
% 1.66/0.59  fof(f20,plain,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.66/0.59    inference(flattening,[],[f19])).
% 1.66/0.59  fof(f19,plain,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.66/0.59    inference(ennf_transformation,[],[f10])).
% 1.66/0.59  fof(f10,axiom,(
% 1.66/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.66/0.59  fof(f376,plain,(
% 1.66/0.59    r1_tarski(sK0,k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 1.66/0.59    inference(forward_demodulation,[],[f375,f65])).
% 1.66/0.59  fof(f65,plain,(
% 1.66/0.59    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))),
% 1.66/0.59    inference(resolution,[],[f34,f39])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f17])).
% 1.66/0.59  fof(f17,plain,(
% 1.66/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f5])).
% 1.66/0.59  fof(f5,axiom,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.66/0.59  fof(f34,plain,(
% 1.66/0.59    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  fof(f375,plain,(
% 1.66/0.59    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 1.66/0.59    inference(forward_demodulation,[],[f374,f318])).
% 1.66/0.59  fof(f374,plain,(
% 1.66/0.59    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2)))),
% 1.66/0.59    inference(forward_demodulation,[],[f373,f318])).
% 1.66/0.59  fof(f373,plain,(
% 1.66/0.59    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 1.66/0.59    inference(resolution,[],[f75,f31])).
% 1.66/0.59  fof(f75,plain,(
% 1.66/0.59    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(sK2,sK0)),k9_relat_1(X1,k10_relat_1(sK2,sK1)))) )),
% 1.66/0.59    inference(resolution,[],[f33,f46])).
% 1.66/0.59  fof(f46,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f24])).
% 1.66/0.59  fof(f24,plain,(
% 1.66/0.59    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.66/0.59    inference(flattening,[],[f23])).
% 1.66/0.59  fof(f23,plain,(
% 1.66/0.59    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.66/0.59    inference(ennf_transformation,[],[f9])).
% 1.66/0.59  fof(f9,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 1.66/0.59  fof(f33,plain,(
% 1.66/0.59    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.66/0.59    inference(cnf_transformation,[],[f28])).
% 1.66/0.59  % SZS output end Proof for theBenchmark
% 1.66/0.59  % (19548)------------------------------
% 1.66/0.59  % (19548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (19548)Termination reason: Refutation
% 1.66/0.59  
% 1.66/0.59  % (19548)Memory used [KB]: 1791
% 1.66/0.59  % (19548)Time elapsed: 0.150 s
% 1.66/0.59  % (19548)------------------------------
% 1.66/0.59  % (19548)------------------------------
% 1.66/0.60  % (19535)Success in time 0.236 s
%------------------------------------------------------------------------------
