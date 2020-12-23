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
% DateTime   : Thu Dec  3 12:53:54 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 188 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  138 ( 489 expanded)
%              Number of equality atoms :   57 (  93 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f32,f166,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f166,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f165,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f84,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f51])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f40,f47])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f165,plain,(
    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f36,f137])).

fof(f137,plain,(
    sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f132,f80])).

fof(f80,plain,(
    sK0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25])).

fof(f25,plain,
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

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k3_xboole_0(k1_relat_1(sK1),X0) = X0 ) ),
    inference(forward_demodulation,[],[f66,f61])).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k1_relat_1(k7_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f39,f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f132,plain,(
    k3_xboole_0(k1_relat_1(sK1),sK0) = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f102,f106])).

fof(f106,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f104,f83])).

fof(f83,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(resolution,[],[f74,f47])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k9_relat_1(k7_relat_1(sK1,X1),X0) = k9_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f35,f30])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f104,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f64,f80])).

fof(f64,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(backward_demodulation,[],[f56,f61])).

fof(f56,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f37,f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

% (27756)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f102,plain,(
    ! [X1] : k3_xboole_0(k1_relat_1(sK1),X1) = k3_xboole_0(X1,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1)))) ),
    inference(superposition,[],[f63,f71])).

fof(f71,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f63,plain,(
    ! [X1] : k10_relat_1(k7_relat_1(sK1,X1),k2_relat_1(k7_relat_1(sK1,X1))) = k3_xboole_0(k1_relat_1(sK1),X1) ),
    inference(backward_demodulation,[],[f57,f61])).

fof(f57,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k10_relat_1(k7_relat_1(sK1,X1),k2_relat_1(k7_relat_1(sK1,X1))) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f32,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:09:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (27747)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (27734)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (27761)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (27754)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.52  % (27753)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.23/0.52  % (27746)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.52  % (27741)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.53  % (27745)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.53  % (27736)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.53  % (27735)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.53  % (27741)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f216,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f32,f166,f44])).
% 1.34/0.53  fof(f44,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.34/0.53    inference(nnf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.34/0.53  fof(f166,plain,(
% 1.34/0.53    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.34/0.53    inference(forward_demodulation,[],[f165,f85])).
% 1.34/0.53  fof(f85,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f84,f53])).
% 1.34/0.53  fof(f53,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.34/0.53    inference(resolution,[],[f45,f47])).
% 1.34/0.53  fof(f47,plain,(
% 1.34/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.53    inference(equality_resolution,[],[f42])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(flattening,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(nnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.53  fof(f45,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f29])).
% 1.34/0.53  fof(f84,plain,(
% 1.34/0.53    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.34/0.53    inference(superposition,[],[f36,f51])).
% 1.34/0.53  fof(f51,plain,(
% 1.34/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.34/0.53    inference(resolution,[],[f40,f47])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.34/0.53  fof(f165,plain,(
% 1.34/0.53    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.34/0.53    inference(superposition,[],[f36,f137])).
% 1.34/0.53  fof(f137,plain,(
% 1.34/0.53    sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.34/0.53    inference(forward_demodulation,[],[f132,f80])).
% 1.34/0.53  fof(f80,plain,(
% 1.34/0.53    sK0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 1.34/0.53    inference(resolution,[],[f68,f31])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.34/0.53    inference(cnf_transformation,[],[f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f15,plain,(
% 1.34/0.54    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.34/0.54    inference(flattening,[],[f14])).
% 1.34/0.54  fof(f14,plain,(
% 1.34/0.54    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.34/0.54    inference(negated_conjecture,[],[f12])).
% 1.34/0.54  fof(f12,conjecture,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.34/0.54  fof(f68,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k3_xboole_0(k1_relat_1(sK1),X0) = X0) )),
% 1.34/0.54    inference(forward_demodulation,[],[f66,f61])).
% 1.34/0.54  fof(f61,plain,(
% 1.34/0.54    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) )),
% 1.34/0.54    inference(resolution,[],[f38,f30])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    v1_relat_1(sK1)),
% 1.34/0.54    inference(cnf_transformation,[],[f26])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f20])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) )),
% 1.34/0.54    inference(resolution,[],[f39,f30])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(flattening,[],[f21])).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.34/0.54  fof(f132,plain,(
% 1.34/0.54    k3_xboole_0(k1_relat_1(sK1),sK0) = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.34/0.54    inference(superposition,[],[f102,f106])).
% 1.34/0.54  fof(f106,plain,(
% 1.34/0.54    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 1.34/0.54    inference(forward_demodulation,[],[f104,f83])).
% 1.34/0.54  fof(f83,plain,(
% 1.34/0.54    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 1.34/0.54    inference(resolution,[],[f74,f47])).
% 1.34/0.54  fof(f74,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k7_relat_1(sK1,X1),X0) = k9_relat_1(sK1,X0)) )),
% 1.34/0.54    inference(resolution,[],[f35,f30])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 1.34/0.54  fof(f104,plain,(
% 1.34/0.54    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 1.34/0.54    inference(superposition,[],[f64,f80])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))) )),
% 1.34/0.54    inference(backward_demodulation,[],[f56,f61])).
% 1.34/0.54  fof(f56,plain,(
% 1.34/0.54    ( ! [X0] : (k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(sK1,X0))) )),
% 1.34/0.54    inference(resolution,[],[f49,f34])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.34/0.54    inference(resolution,[],[f37,f30])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.34/0.54  % (27756)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    ( ! [X1] : (k3_xboole_0(k1_relat_1(sK1),X1) = k3_xboole_0(X1,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1))))) )),
% 1.34/0.54    inference(superposition,[],[f63,f71])).
% 1.34/0.54  fof(f71,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 1.34/0.54    inference(resolution,[],[f46,f30])).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.34/0.54    inference(ennf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.34/0.54  fof(f63,plain,(
% 1.34/0.54    ( ! [X1] : (k10_relat_1(k7_relat_1(sK1,X1),k2_relat_1(k7_relat_1(sK1,X1))) = k3_xboole_0(k1_relat_1(sK1),X1)) )),
% 1.34/0.54    inference(backward_demodulation,[],[f57,f61])).
% 1.34/0.54  fof(f57,plain,(
% 1.34/0.54    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k10_relat_1(k7_relat_1(sK1,X1),k2_relat_1(k7_relat_1(sK1,X1)))) )),
% 1.34/0.54    inference(resolution,[],[f49,f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,plain,(
% 1.34/0.54    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.34/0.54    inference(cnf_transformation,[],[f26])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (27741)------------------------------
% 1.34/0.54  % (27741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (27741)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (27741)Memory used [KB]: 1918
% 1.34/0.54  % (27741)Time elapsed: 0.124 s
% 1.34/0.54  % (27741)------------------------------
% 1.34/0.54  % (27741)------------------------------
% 1.34/0.54  % (27733)Success in time 0.175 s
%------------------------------------------------------------------------------
