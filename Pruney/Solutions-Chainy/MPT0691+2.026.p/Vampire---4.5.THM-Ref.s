%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:48 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 129 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 326 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f978,plain,(
    $false ),
    inference(subsumption_resolution,[],[f977,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f977,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f943,f711])).

fof(f711,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f708,f68])).

fof(f68,plain,(
    ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X5)),X5) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f38])).

fof(f38,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f708,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f691,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f691,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f498,f79])).

fof(f79,plain,(
    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f43,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f43,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f498,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f126,f75])).

fof(f75,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f42,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f126,plain,(
    ! [X4,X3] : r1_tarski(k3_xboole_0(X3,k10_relat_1(sK1,X4)),k1_relat_1(k7_relat_1(sK1,X3))) ),
    inference(forward_demodulation,[],[f113,f64])).

fof(f64,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f42,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f113,plain,(
    ! [X4,X3] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X3),X4),k1_relat_1(k7_relat_1(sK1,X3))) ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f69,plain,(
    ! [X6] : v1_relat_1(k7_relat_1(sK1,X6)) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f943,plain,(
    ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f235,f313])).

fof(f313,plain,(
    ! [X4] : k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k9_relat_1(sK1,X4))) ),
    inference(forward_demodulation,[],[f312,f66])).

fof(f66,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(sK1,X3)) = k9_relat_1(sK1,X3) ),
    inference(resolution,[],[f42,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f312,plain,(
    ! [X4] : k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X4)))) ),
    inference(subsumption_resolution,[],[f306,f69])).

fof(f306,plain,(
    ! [X4] :
      ( k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X4))))
      | ~ v1_relat_1(k7_relat_1(sK1,X4)) ) ),
    inference(superposition,[],[f64,f61])).

fof(f235,plain,(
    ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) ),
    inference(superposition,[],[f111,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f111,plain,(
    ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f44,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (14865)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (14866)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (14867)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (14862)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (14863)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (14878)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.21/0.52  % (14879)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.21/0.52  % (14875)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.21/0.52  % (14876)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.21/0.52  % (14869)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.21/0.52  % (14883)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.21/0.52  % (14887)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.21/0.52  % (14882)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.21/0.52  % (14872)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.21/0.53  % (14880)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.21/0.53  % (14873)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.21/0.53  % (14864)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.21/0.53  % (14889)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.21/0.53  % (14881)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.21/0.53  % (14874)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.36/0.54  % (14888)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.36/0.54  % (14884)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.36/0.55  % (14871)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.36/0.55  % (14877)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.36/0.55  % (14868)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.36/0.55  % (14886)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.36/0.56  % (14874)Refutation found. Thanks to Tanya!
% 1.36/0.56  % SZS status Theorem for theBenchmark
% 1.36/0.57  % SZS output start Proof for theBenchmark
% 1.36/0.57  fof(f978,plain,(
% 1.36/0.57    $false),
% 1.36/0.57    inference(subsumption_resolution,[],[f977,f63])).
% 1.36/0.57  fof(f63,plain,(
% 1.36/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.57    inference(equality_resolution,[],[f48])).
% 1.36/0.57  fof(f48,plain,(
% 1.36/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.36/0.57    inference(cnf_transformation,[],[f41])).
% 1.36/0.57  fof(f41,plain,(
% 1.36/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.57    inference(flattening,[],[f40])).
% 1.36/0.57  fof(f40,plain,(
% 1.36/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.57    inference(nnf_transformation,[],[f2])).
% 1.36/0.57  fof(f2,axiom,(
% 1.36/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.57  fof(f977,plain,(
% 1.36/0.57    ~r1_tarski(sK0,sK0)),
% 1.36/0.57    inference(forward_demodulation,[],[f943,f711])).
% 1.36/0.57  fof(f711,plain,(
% 1.36/0.57    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.36/0.57    inference(subsumption_resolution,[],[f708,f68])).
% 1.36/0.57  fof(f68,plain,(
% 1.36/0.57    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X5)),X5)) )),
% 1.36/0.57    inference(resolution,[],[f42,f56])).
% 1.36/0.57  fof(f56,plain,(
% 1.36/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f32])).
% 1.36/0.57  fof(f32,plain,(
% 1.36/0.57    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f17])).
% 1.36/0.57  fof(f17,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.36/0.57  fof(f42,plain,(
% 1.36/0.57    v1_relat_1(sK1)),
% 1.36/0.57    inference(cnf_transformation,[],[f39])).
% 1.36/0.57  fof(f39,plain,(
% 1.36/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.36/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f38])).
% 1.36/0.57  fof(f38,plain,(
% 1.36/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.36/0.57    introduced(choice_axiom,[])).
% 1.36/0.57  fof(f23,plain,(
% 1.36/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.36/0.57    inference(flattening,[],[f22])).
% 1.36/0.57  fof(f22,plain,(
% 1.36/0.57    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f21])).
% 1.36/0.57  fof(f21,negated_conjecture,(
% 1.36/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.36/0.57    inference(negated_conjecture,[],[f20])).
% 1.36/0.57  fof(f20,conjecture,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.36/0.57  fof(f708,plain,(
% 1.36/0.57    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)),
% 1.36/0.57    inference(resolution,[],[f691,f50])).
% 1.36/0.57  fof(f50,plain,(
% 1.36/0.57    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f41])).
% 1.36/0.57  fof(f691,plain,(
% 1.36/0.57    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.36/0.57    inference(superposition,[],[f498,f79])).
% 1.36/0.57  fof(f79,plain,(
% 1.36/0.57    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 1.36/0.57    inference(resolution,[],[f43,f53])).
% 1.36/0.57  fof(f53,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f29])).
% 1.36/0.57  fof(f29,plain,(
% 1.36/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f8])).
% 1.36/0.57  fof(f8,axiom,(
% 1.36/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.36/0.57  fof(f43,plain,(
% 1.36/0.57    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.36/0.57    inference(cnf_transformation,[],[f39])).
% 1.36/0.57  fof(f498,plain,(
% 1.36/0.57    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.36/0.57    inference(superposition,[],[f126,f75])).
% 1.36/0.57  fof(f75,plain,(
% 1.36/0.57    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 1.36/0.57    inference(resolution,[],[f42,f61])).
% 1.36/0.57  fof(f61,plain,(
% 1.36/0.57    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f37])).
% 1.36/0.57  fof(f37,plain,(
% 1.36/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f14])).
% 1.36/0.57  fof(f14,axiom,(
% 1.36/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.36/0.57  fof(f126,plain,(
% 1.36/0.57    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(X3,k10_relat_1(sK1,X4)),k1_relat_1(k7_relat_1(sK1,X3)))) )),
% 1.36/0.57    inference(forward_demodulation,[],[f113,f64])).
% 1.36/0.57  fof(f64,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 1.36/0.57    inference(resolution,[],[f42,f45])).
% 1.36/0.57  fof(f45,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f24])).
% 1.36/0.57  fof(f24,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.36/0.57    inference(ennf_transformation,[],[f19])).
% 1.36/0.57  fof(f19,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.36/0.57  fof(f113,plain,(
% 1.36/0.57    ( ! [X4,X3] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X3),X4),k1_relat_1(k7_relat_1(sK1,X3)))) )),
% 1.36/0.57    inference(resolution,[],[f69,f46])).
% 1.36/0.57  fof(f46,plain,(
% 1.36/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f25])).
% 1.36/0.57  fof(f25,plain,(
% 1.36/0.57    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f13])).
% 1.36/0.57  fof(f13,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.36/0.57  fof(f69,plain,(
% 1.36/0.57    ( ! [X6] : (v1_relat_1(k7_relat_1(sK1,X6))) )),
% 1.36/0.57    inference(resolution,[],[f42,f57])).
% 1.36/0.57  fof(f57,plain,(
% 1.36/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f33])).
% 1.36/0.57  fof(f33,plain,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f11])).
% 1.36/0.57  fof(f11,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.36/0.57  fof(f943,plain,(
% 1.36/0.57    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.36/0.57    inference(superposition,[],[f235,f313])).
% 1.36/0.57  fof(f313,plain,(
% 1.36/0.57    ( ! [X4] : (k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k9_relat_1(sK1,X4)))) )),
% 1.36/0.57    inference(forward_demodulation,[],[f312,f66])).
% 1.36/0.57  fof(f66,plain,(
% 1.36/0.57    ( ! [X3] : (k2_relat_1(k7_relat_1(sK1,X3)) = k9_relat_1(sK1,X3)) )),
% 1.36/0.57    inference(resolution,[],[f42,f47])).
% 1.36/0.57  fof(f47,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f26])).
% 1.36/0.57  fof(f26,plain,(
% 1.36/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f12])).
% 1.36/0.57  fof(f12,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.36/0.57  fof(f312,plain,(
% 1.36/0.57    ( ! [X4] : (k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X4))))) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f306,f69])).
% 1.36/0.57  fof(f306,plain,(
% 1.36/0.57    ( ! [X4] : (k1_relat_1(k7_relat_1(sK1,X4)) = k3_xboole_0(X4,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X4)))) | ~v1_relat_1(k7_relat_1(sK1,X4))) )),
% 1.36/0.57    inference(superposition,[],[f64,f61])).
% 1.36/0.57  fof(f235,plain,(
% 1.36/0.57    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) )),
% 1.36/0.57    inference(superposition,[],[f111,f54])).
% 1.36/0.57  fof(f54,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f1])).
% 1.36/0.57  fof(f1,axiom,(
% 1.36/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.36/0.57  fof(f111,plain,(
% 1.36/0.57    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0))) )),
% 1.36/0.57    inference(resolution,[],[f44,f51])).
% 1.36/0.57  fof(f51,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.36/0.57    inference(cnf_transformation,[],[f27])).
% 1.36/0.57  fof(f27,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.36/0.57    inference(ennf_transformation,[],[f7])).
% 1.36/0.57  fof(f7,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.36/0.57  fof(f44,plain,(
% 1.36/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.36/0.57    inference(cnf_transformation,[],[f39])).
% 1.36/0.57  % SZS output end Proof for theBenchmark
% 1.36/0.57  % (14874)------------------------------
% 1.36/0.57  % (14874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (14874)Termination reason: Refutation
% 1.36/0.57  
% 1.36/0.57  % (14874)Memory used [KB]: 11385
% 1.36/0.57  % (14874)Time elapsed: 0.145 s
% 1.36/0.57  % (14874)------------------------------
% 1.36/0.57  % (14874)------------------------------
% 1.36/0.57  % (14859)Success in time 0.209 s
%------------------------------------------------------------------------------
