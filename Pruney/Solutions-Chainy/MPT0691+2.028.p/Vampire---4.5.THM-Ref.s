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
% DateTime   : Thu Dec  3 12:53:48 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 134 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   21
%              Number of atoms          :  155 ( 335 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f630,plain,(
    $false ),
    inference(subsumption_resolution,[],[f629,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f29])).

fof(f29,plain,
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

fof(f629,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f628,f34])).

fof(f34,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f628,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f626,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f626,plain,(
    ! [X1] : ~ r1_tarski(sK0,k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f624,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f624,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,sK0)
      | ~ r1_tarski(sK0,k10_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f608,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f608,plain,(
    ! [X8] : ~ r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X8))) ),
    inference(subsumption_resolution,[],[f605,f33])).

fof(f605,plain,(
    ! [X8] :
      ( ~ r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X8)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f598,f177])).

fof(f177,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9)))
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f172,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f172,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9)))
      | ~ v1_relat_1(k7_relat_1(X8,X9))
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f40,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
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

fof(f40,plain,(
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

fof(f598,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,sK0)))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f596,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f50,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f596,plain,(
    ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f484,f51])).

fof(f484,plain,(
    ! [X2] :
      ( ~ r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,sK0))
      | ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,X2))) ) ),
    inference(subsumption_resolution,[],[f482,f33])).

fof(f482,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,X2)))
      | ~ r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,sK0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f476,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f118,f39])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f36,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f476,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X1),X0))
      | ~ r1_tarski(X0,k9_relat_1(sK1,sK0)) ) ),
    inference(subsumption_resolution,[],[f456,f33])).

fof(f456,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k9_relat_1(sK1,sK0))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X1),X0)) ) ),
    inference(resolution,[],[f175,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f128,f67])).

fof(f128,plain,(
    ! [X3] : ~ r1_tarski(sK0,k3_xboole_0(X3,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) ),
    inference(resolution,[],[f112,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f112,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      | ~ r1_tarski(sK0,X8) ) ),
    inference(resolution,[],[f67,f35])).

fof(f35,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X3),k3_xboole_0(X1,k10_relat_1(X0,X2)))
      | ~ r1_tarski(X3,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f170,f39])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X3),k3_xboole_0(X1,k10_relat_1(X0,X2)))
      | ~ r1_tarski(X3,X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f48,f47])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (12566)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (12579)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (12568)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (12569)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (12589)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (12570)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (12578)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (12584)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (12571)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (12582)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (12588)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (12576)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (12586)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (12591)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (12573)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (12580)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (12575)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.32/0.54  % (12590)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.32/0.54  % (12587)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.32/0.54  % (12572)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.32/0.54  % (12567)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (12574)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.32/0.55  % (12577)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.32/0.55  % (12583)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.32/0.55  % (12585)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.32/0.56  % (12581)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.62/0.58  % (12570)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.59  fof(f630,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(subsumption_resolution,[],[f629,f33])).
% 1.62/0.59  fof(f33,plain,(
% 1.62/0.59    v1_relat_1(sK1)),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f30,plain,(
% 1.62/0.59    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f29])).
% 1.62/0.59  fof(f29,plain,(
% 1.62/0.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f17,plain,(
% 1.62/0.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.62/0.59    inference(flattening,[],[f16])).
% 1.62/0.59  fof(f16,plain,(
% 1.62/0.59    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f15])).
% 1.62/0.59  fof(f15,negated_conjecture,(
% 1.62/0.59    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.62/0.59    inference(negated_conjecture,[],[f14])).
% 1.62/0.59  fof(f14,conjecture,(
% 1.62/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.62/0.59  fof(f629,plain,(
% 1.62/0.59    ~v1_relat_1(sK1)),
% 1.62/0.59    inference(subsumption_resolution,[],[f628,f34])).
% 1.62/0.59  fof(f34,plain,(
% 1.62/0.59    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f628,plain,(
% 1.62/0.59    ~r1_tarski(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.62/0.59    inference(superposition,[],[f626,f36])).
% 1.62/0.59  fof(f36,plain,(
% 1.62/0.59    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f18])).
% 1.62/0.59  fof(f18,plain,(
% 1.62/0.59    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f11])).
% 1.62/0.59  fof(f11,axiom,(
% 1.62/0.59    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.62/0.59  fof(f626,plain,(
% 1.62/0.59    ( ! [X1] : (~r1_tarski(sK0,k10_relat_1(sK1,X1))) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f624,f51])).
% 1.62/0.59  fof(f51,plain,(
% 1.62/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.62/0.59    inference(equality_resolution,[],[f45])).
% 1.62/0.59  fof(f45,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.62/0.59    inference(cnf_transformation,[],[f32])).
% 1.62/0.59  fof(f32,plain,(
% 1.62/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.59    inference(flattening,[],[f31])).
% 1.62/0.59  fof(f31,plain,(
% 1.62/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.59    inference(nnf_transformation,[],[f2])).
% 1.62/0.59  fof(f2,axiom,(
% 1.62/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.62/0.59  fof(f624,plain,(
% 1.62/0.59    ( ! [X1] : (~r1_tarski(sK0,sK0) | ~r1_tarski(sK0,k10_relat_1(sK1,X1))) )),
% 1.62/0.59    inference(superposition,[],[f608,f43])).
% 1.62/0.59  fof(f43,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f23])).
% 1.62/0.59  fof(f23,plain,(
% 1.62/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f7])).
% 1.62/0.59  fof(f7,axiom,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.62/0.59  fof(f608,plain,(
% 1.62/0.59    ( ! [X8] : (~r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X8)))) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f605,f33])).
% 1.62/0.59  fof(f605,plain,(
% 1.62/0.59    ( ! [X8] : (~r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X8))) | ~v1_relat_1(sK1)) )),
% 1.62/0.59    inference(resolution,[],[f598,f177])).
% 1.62/0.59  fof(f177,plain,(
% 1.62/0.59    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9))) | ~v1_relat_1(X8)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f172,f39])).
% 1.62/0.59  fof(f39,plain,(
% 1.62/0.59    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f8])).
% 1.62/0.59  fof(f8,axiom,(
% 1.62/0.59    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.62/0.59  fof(f172,plain,(
% 1.62/0.59    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9))) | ~v1_relat_1(k7_relat_1(X8,X9)) | ~v1_relat_1(X8)) )),
% 1.62/0.59    inference(superposition,[],[f40,f47])).
% 1.62/0.59  fof(f47,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f24])).
% 1.62/0.59  fof(f24,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.62/0.59    inference(ennf_transformation,[],[f13])).
% 1.62/0.59  fof(f13,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.62/0.59  fof(f40,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f20])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f10])).
% 1.62/0.59  fof(f10,axiom,(
% 1.62/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.62/0.59  fof(f598,plain,(
% 1.62/0.59    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~r1_tarski(sK0,X0)) )),
% 1.62/0.59    inference(resolution,[],[f596,f67])).
% 1.62/0.59  fof(f67,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(superposition,[],[f50,f42])).
% 1.62/0.59  fof(f42,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f22])).
% 1.62/0.59  fof(f22,plain,(
% 1.62/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f5])).
% 1.62/0.59  fof(f5,axiom,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.62/0.59  fof(f50,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f28])).
% 1.62/0.59  fof(f28,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.62/0.59    inference(ennf_transformation,[],[f4])).
% 1.62/0.59  fof(f4,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.62/0.59  fof(f596,plain,(
% 1.62/0.59    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.62/0.59    inference(resolution,[],[f484,f51])).
% 1.62/0.59  fof(f484,plain,(
% 1.62/0.59    ( ! [X2] : (~r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,sK0)) | ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,X2)))) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f482,f33])).
% 1.62/0.59  fof(f482,plain,(
% 1.62/0.59    ( ! [X2] : (~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,X2))) | ~r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)) )),
% 1.62/0.59    inference(superposition,[],[f476,f119])).
% 1.62/0.59  fof(f119,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f118,f39])).
% 1.62/0.59  fof(f118,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(superposition,[],[f36,f41])).
% 1.62/0.59  fof(f41,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f21])).
% 1.62/0.59  fof(f21,plain,(
% 1.62/0.59    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f9])).
% 1.62/0.59  fof(f9,axiom,(
% 1.62/0.59    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.62/0.59  fof(f476,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X1),X0)) | ~r1_tarski(X0,k9_relat_1(sK1,sK0))) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f456,f33])).
% 1.62/0.59  fof(f456,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X1),X0))) )),
% 1.62/0.59    inference(resolution,[],[f175,f136])).
% 1.62/0.59  fof(f136,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) | ~r1_tarski(sK0,X0)) )),
% 1.62/0.59    inference(resolution,[],[f128,f67])).
% 1.62/0.59  fof(f128,plain,(
% 1.62/0.59    ( ! [X3] : (~r1_tarski(sK0,k3_xboole_0(X3,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) )),
% 1.62/0.59    inference(resolution,[],[f112,f53])).
% 1.62/0.59  fof(f53,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.62/0.59    inference(superposition,[],[f37,f38])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f1])).
% 1.62/0.59  fof(f1,axiom,(
% 1.62/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.62/0.59  fof(f37,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f6])).
% 1.62/0.59  fof(f6,axiom,(
% 1.62/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.62/0.59  fof(f112,plain,(
% 1.62/0.59    ( ! [X8] : (~r1_tarski(X8,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~r1_tarski(sK0,X8)) )),
% 1.62/0.59    inference(resolution,[],[f67,f35])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f175,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X3),k3_xboole_0(X1,k10_relat_1(X0,X2))) | ~r1_tarski(X3,X2) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f170,f39])).
% 1.62/0.59  fof(f170,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X3),k3_xboole_0(X1,k10_relat_1(X0,X2))) | ~r1_tarski(X3,X2) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(superposition,[],[f48,f47])).
% 1.62/0.59  fof(f48,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f26])).
% 1.62/0.59  fof(f26,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.62/0.59    inference(flattening,[],[f25])).
% 1.62/0.59  fof(f25,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.62/0.59    inference(ennf_transformation,[],[f12])).
% 1.62/0.59  fof(f12,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (12570)------------------------------
% 1.62/0.59  % (12570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (12570)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (12570)Memory used [KB]: 6396
% 1.62/0.59  % (12570)Time elapsed: 0.146 s
% 1.62/0.59  % (12570)------------------------------
% 1.62/0.59  % (12570)------------------------------
% 1.62/0.59  % (12565)Success in time 0.231 s
%------------------------------------------------------------------------------
