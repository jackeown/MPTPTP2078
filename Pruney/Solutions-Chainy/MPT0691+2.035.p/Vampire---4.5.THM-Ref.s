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
% DateTime   : Thu Dec  3 12:53:49 EST 2020

% Result     : Theorem 3.26s
% Output     : Refutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 191 expanded)
%              Number of leaves         :   11 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  117 ( 468 expanded)
%              Number of equality atoms :   40 (  73 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5160,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5147,f32])).

fof(f32,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f5147,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f859,f4789])).

fof(f4789,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f4786,f858])).

fof(f858,plain,(
    ! [X2] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),X2) ),
    inference(superposition,[],[f34,f266])).

fof(f266,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1))) ),
    inference(forward_demodulation,[],[f264,f72])).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f37,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f264,plain,(
    ! [X1] : k3_xboole_0(X1,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1)))) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(superposition,[],[f59,f78])).

fof(f78,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f43,f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f59,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f36,f30])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f4786,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f4593,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4593,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f4442,f52])).

fof(f52,plain,(
    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f4442,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f1555,f58])).

fof(f58,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f33,f30])).

fof(f1555,plain,(
    ! [X6,X5] : r1_tarski(k3_xboole_0(X5,k10_relat_1(sK1,X6)),k1_relat_1(k7_relat_1(sK1,X5))) ),
    inference(superposition,[],[f34,f292])).

fof(f292,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k10_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) ),
    inference(forward_demodulation,[],[f290,f78])).

fof(f290,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) ),
    inference(superposition,[],[f80,f124])).

fof(f124,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f74,f48])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f80,plain,(
    ! [X4,X2,X3] : k10_relat_1(k7_relat_1(k7_relat_1(sK1,X2),X3),X4) = k3_xboole_0(X3,k3_xboole_0(X2,k10_relat_1(sK1,X4))) ),
    inference(forward_demodulation,[],[f79,f78])).

fof(f79,plain,(
    ! [X4,X2,X3] : k10_relat_1(k7_relat_1(k7_relat_1(sK1,X2),X3),X4) = k3_xboole_0(X3,k10_relat_1(k7_relat_1(sK1,X2),X4)) ),
    inference(resolution,[],[f43,f48])).

fof(f859,plain,(
    ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X5)),k10_relat_1(sK1,k9_relat_1(sK1,X5))) ),
    inference(superposition,[],[f49,f266])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:09:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.46  % (19148)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.46  % (19140)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.48  % (19135)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.48  % (19136)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.48  % (19133)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (19151)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.49  % (19144)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.49  % (19143)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.50  % (19149)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.50  % (19152)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.50  % (19141)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.51  % (19137)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.51  % (19154)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.52  % (19146)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.52  % (19132)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.52  % (19150)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.52  % (19142)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.52  % (19156)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.52  % (19153)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.53  % (19138)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.53  % (19147)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.53  % (19157)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.53  % (19134)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.53  % (19155)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.54  % (19139)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.54  % (19145)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.83/0.61  % (19141)Refutation not found, incomplete strategy% (19141)------------------------------
% 1.83/0.61  % (19141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.61  % (19141)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.61  
% 1.83/0.61  % (19141)Memory used [KB]: 6140
% 1.83/0.61  % (19141)Time elapsed: 0.218 s
% 1.83/0.61  % (19141)------------------------------
% 1.83/0.61  % (19141)------------------------------
% 3.26/0.82  % (19142)Refutation found. Thanks to Tanya!
% 3.26/0.82  % SZS status Theorem for theBenchmark
% 3.26/0.82  % SZS output start Proof for theBenchmark
% 3.26/0.82  fof(f5160,plain,(
% 3.26/0.82    $false),
% 3.26/0.82    inference(subsumption_resolution,[],[f5147,f32])).
% 3.26/0.82  fof(f32,plain,(
% 3.26/0.82    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.26/0.82    inference(cnf_transformation,[],[f27])).
% 3.26/0.82  fof(f27,plain,(
% 3.26/0.82    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 3.26/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f26])).
% 3.26/0.82  fof(f26,plain,(
% 3.26/0.82    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 3.26/0.82    introduced(choice_axiom,[])).
% 3.26/0.82  fof(f15,plain,(
% 3.26/0.82    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 3.26/0.82    inference(flattening,[],[f14])).
% 3.26/0.82  fof(f14,plain,(
% 3.26/0.82    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 3.26/0.82    inference(ennf_transformation,[],[f13])).
% 3.26/0.82  fof(f13,negated_conjecture,(
% 3.26/0.82    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.26/0.82    inference(negated_conjecture,[],[f12])).
% 3.26/0.82  fof(f12,conjecture,(
% 3.26/0.82    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 3.26/0.82  fof(f5147,plain,(
% 3.26/0.82    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.26/0.82    inference(superposition,[],[f859,f4789])).
% 3.26/0.82  fof(f4789,plain,(
% 3.26/0.82    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 3.26/0.82    inference(subsumption_resolution,[],[f4786,f858])).
% 3.26/0.82  fof(f858,plain,(
% 3.26/0.82    ( ! [X2] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),X2)) )),
% 3.26/0.82    inference(superposition,[],[f34,f266])).
% 3.26/0.82  fof(f266,plain,(
% 3.26/0.82    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1)))) )),
% 3.26/0.82    inference(forward_demodulation,[],[f264,f72])).
% 3.26/0.82  fof(f72,plain,(
% 3.26/0.82    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 3.26/0.82    inference(resolution,[],[f37,f30])).
% 3.26/0.82  fof(f30,plain,(
% 3.26/0.82    v1_relat_1(sK1)),
% 3.26/0.82    inference(cnf_transformation,[],[f27])).
% 3.26/0.82  fof(f37,plain,(
% 3.26/0.82    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 3.26/0.82    inference(cnf_transformation,[],[f18])).
% 3.26/0.82  fof(f18,plain,(
% 3.26/0.82    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.26/0.82    inference(ennf_transformation,[],[f7])).
% 3.26/0.82  fof(f7,axiom,(
% 3.26/0.82    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 3.26/0.82  fof(f264,plain,(
% 3.26/0.82    ( ! [X1] : (k3_xboole_0(X1,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1)))) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 3.26/0.82    inference(superposition,[],[f59,f78])).
% 3.26/0.82  fof(f78,plain,(
% 3.26/0.82    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 3.26/0.82    inference(resolution,[],[f43,f30])).
% 3.26/0.82  fof(f43,plain,(
% 3.26/0.82    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 3.26/0.82    inference(cnf_transformation,[],[f22])).
% 3.26/0.82  fof(f22,plain,(
% 3.26/0.82    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.26/0.82    inference(ennf_transformation,[],[f11])).
% 3.26/0.82  fof(f11,axiom,(
% 3.26/0.82    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 3.26/0.82  fof(f59,plain,(
% 3.26/0.82    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 3.26/0.82    inference(resolution,[],[f33,f48])).
% 3.26/0.82  fof(f48,plain,(
% 3.26/0.82    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 3.26/0.82    inference(resolution,[],[f36,f30])).
% 3.26/0.82  fof(f36,plain,(
% 3.26/0.82    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 3.26/0.82    inference(cnf_transformation,[],[f17])).
% 3.26/0.82  fof(f17,plain,(
% 3.26/0.82    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.26/0.82    inference(ennf_transformation,[],[f6])).
% 3.26/0.82  fof(f6,axiom,(
% 3.26/0.82    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.26/0.82  fof(f33,plain,(
% 3.26/0.82    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 3.26/0.82    inference(cnf_transformation,[],[f16])).
% 3.26/0.82  fof(f16,plain,(
% 3.26/0.82    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.26/0.82    inference(ennf_transformation,[],[f8])).
% 3.26/0.82  fof(f8,axiom,(
% 3.26/0.82    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 3.26/0.82  fof(f34,plain,(
% 3.26/0.82    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.26/0.82    inference(cnf_transformation,[],[f4])).
% 3.26/0.82  fof(f4,axiom,(
% 3.26/0.82    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.26/0.82  fof(f4786,plain,(
% 3.26/0.82    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)),
% 3.26/0.82    inference(resolution,[],[f4593,f42])).
% 3.26/0.82  fof(f42,plain,(
% 3.26/0.82    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.26/0.82    inference(cnf_transformation,[],[f29])).
% 3.26/0.82  fof(f29,plain,(
% 3.26/0.82    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.26/0.82    inference(flattening,[],[f28])).
% 3.26/0.82  fof(f28,plain,(
% 3.26/0.82    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.26/0.82    inference(nnf_transformation,[],[f2])).
% 3.26/0.82  fof(f2,axiom,(
% 3.26/0.82    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.26/0.82  fof(f4593,plain,(
% 3.26/0.82    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 3.26/0.82    inference(superposition,[],[f4442,f52])).
% 3.26/0.82  fof(f52,plain,(
% 3.26/0.82    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 3.26/0.82    inference(resolution,[],[f39,f31])).
% 3.26/0.82  fof(f31,plain,(
% 3.26/0.82    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.26/0.82    inference(cnf_transformation,[],[f27])).
% 3.26/0.82  fof(f39,plain,(
% 3.26/0.82    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.26/0.82    inference(cnf_transformation,[],[f21])).
% 3.26/0.82  fof(f21,plain,(
% 3.26/0.82    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.26/0.82    inference(ennf_transformation,[],[f5])).
% 3.26/0.82  fof(f5,axiom,(
% 3.26/0.82    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.26/0.82  fof(f4442,plain,(
% 3.26/0.82    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 3.26/0.82    inference(superposition,[],[f1555,f58])).
% 3.26/0.82  fof(f58,plain,(
% 3.26/0.82    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 3.26/0.82    inference(resolution,[],[f33,f30])).
% 3.26/0.82  fof(f1555,plain,(
% 3.26/0.82    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X5,k10_relat_1(sK1,X6)),k1_relat_1(k7_relat_1(sK1,X5)))) )),
% 3.26/0.82    inference(superposition,[],[f34,f292])).
% 3.26/0.82  fof(f292,plain,(
% 3.26/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,k10_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1)))) )),
% 3.26/0.82    inference(forward_demodulation,[],[f290,f78])).
% 3.26/0.82  fof(f290,plain,(
% 3.26/0.82    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1)))) )),
% 3.26/0.82    inference(superposition,[],[f80,f124])).
% 3.26/0.82  fof(f124,plain,(
% 3.26/0.82    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 3.26/0.82    inference(resolution,[],[f74,f48])).
% 3.26/0.82  fof(f74,plain,(
% 3.26/0.82    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 3.26/0.82    inference(resolution,[],[f38,f46])).
% 3.26/0.82  fof(f46,plain,(
% 3.26/0.82    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.26/0.82    inference(equality_resolution,[],[f41])).
% 3.26/0.82  fof(f41,plain,(
% 3.26/0.82    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.26/0.82    inference(cnf_transformation,[],[f29])).
% 3.26/0.82  fof(f38,plain,(
% 3.26/0.82    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 3.26/0.82    inference(cnf_transformation,[],[f20])).
% 3.26/0.82  fof(f20,plain,(
% 3.26/0.82    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.26/0.82    inference(flattening,[],[f19])).
% 3.26/0.82  fof(f19,plain,(
% 3.26/0.82    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.26/0.82    inference(ennf_transformation,[],[f10])).
% 3.26/0.82  fof(f10,axiom,(
% 3.26/0.82    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 3.26/0.82  fof(f80,plain,(
% 3.26/0.82    ( ! [X4,X2,X3] : (k10_relat_1(k7_relat_1(k7_relat_1(sK1,X2),X3),X4) = k3_xboole_0(X3,k3_xboole_0(X2,k10_relat_1(sK1,X4)))) )),
% 3.26/0.82    inference(forward_demodulation,[],[f79,f78])).
% 3.26/0.82  fof(f79,plain,(
% 3.26/0.82    ( ! [X4,X2,X3] : (k10_relat_1(k7_relat_1(k7_relat_1(sK1,X2),X3),X4) = k3_xboole_0(X3,k10_relat_1(k7_relat_1(sK1,X2),X4))) )),
% 3.26/0.82    inference(resolution,[],[f43,f48])).
% 3.26/0.82  fof(f859,plain,(
% 3.26/0.82    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X5)),k10_relat_1(sK1,k9_relat_1(sK1,X5)))) )),
% 3.26/0.82    inference(superposition,[],[f49,f266])).
% 3.26/0.82  fof(f49,plain,(
% 3.26/0.82    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.26/0.82    inference(superposition,[],[f34,f35])).
% 3.26/0.82  fof(f35,plain,(
% 3.26/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.26/0.82    inference(cnf_transformation,[],[f1])).
% 3.26/0.82  fof(f1,axiom,(
% 3.26/0.82    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.26/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.26/0.82  % SZS output end Proof for theBenchmark
% 3.26/0.82  % (19142)------------------------------
% 3.26/0.82  % (19142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.82  % (19142)Termination reason: Refutation
% 3.26/0.82  
% 3.26/0.82  % (19142)Memory used [KB]: 14328
% 3.26/0.82  % (19142)Time elapsed: 0.408 s
% 3.26/0.82  % (19142)------------------------------
% 3.26/0.82  % (19142)------------------------------
% 3.26/0.82  % (19131)Success in time 0.48 s
%------------------------------------------------------------------------------
