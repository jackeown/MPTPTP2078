%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 104 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 269 expanded)
%              Number of equality atoms :   39 (  88 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,(
    k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) != k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f49,f174])).

fof(f174,plain,(
    ! [X2,X3] : k3_xboole_0(X3,k9_relat_1(sK2,X2)) = k9_relat_1(sK2,k3_xboole_0(X2,k10_relat_1(sK2,X3))) ),
    inference(superposition,[],[f147,f105])).

fof(f105,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),k3_xboole_0(X0,X1)) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,X1) ) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

fof(f147,plain,(
    ! [X2,X1] : k3_xboole_0(X2,k9_relat_1(sK2,X1)) = k9_relat_1(k7_relat_1(sK2,X1),k3_xboole_0(X1,k10_relat_1(sK2,X2))) ),
    inference(forward_demodulation,[],[f146,f57])).

fof(f57,plain,(
    ! [X8,X7] : k10_relat_1(k7_relat_1(sK2,X7),X8) = k3_xboole_0(X7,k10_relat_1(sK2,X8)) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f146,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k3_xboole_0(X2,k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f145,f52])).

fof(f52,plain,(
    ! [X2] : v1_relat_1(k7_relat_1(sK2,X2)) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f145,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k3_xboole_0(X2,k9_relat_1(sK2,X1))
      | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f141,f61])).

fof(f61,plain,(
    ! [X1] : v1_funct_1(k7_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f59,f30])).

fof(f59,plain,(
    ! [X1] :
      ( v1_funct_1(k7_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f31,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k3_xboole_0(X2,k9_relat_1(sK2,X1))
      | ~ v1_funct_1(k7_relat_1(sK2,X1))
      | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f40,f137])).

fof(f137,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0) ),
    inference(forward_demodulation,[],[f63,f53])).

fof(f53,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f63,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f52,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f40,plain,(
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

fof(f49,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f32,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:20:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.54  % (2061)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (2060)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (2057)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (2059)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (2077)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (2076)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.55  % (2063)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (2075)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (2070)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (2073)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (2069)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.55  % (2062)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (2068)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (2071)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.56  % (2067)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.56  % (2055)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (2065)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (2054)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (2060)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f189,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f188])).
% 0.22/0.57  fof(f188,plain,(
% 0.22/0.57    k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) != k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),
% 0.22/0.57    inference(superposition,[],[f49,f174])).
% 0.22/0.57  fof(f174,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k3_xboole_0(X3,k9_relat_1(sK2,X2)) = k9_relat_1(sK2,k3_xboole_0(X2,k10_relat_1(sK2,X3)))) )),
% 0.22/0.57    inference(superposition,[],[f147,f105])).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),k3_xboole_0(X0,X1)) = k9_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(resolution,[],[f51,f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,X1)) )),
% 0.22/0.57    inference(resolution,[],[f30,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    v1_relat_1(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.57    inference(flattening,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 0.22/0.57    inference(negated_conjecture,[],[f12])).
% 0.22/0.57  fof(f12,conjecture,(
% 0.22/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).
% 0.22/0.57  fof(f147,plain,(
% 0.22/0.57    ( ! [X2,X1] : (k3_xboole_0(X2,k9_relat_1(sK2,X1)) = k9_relat_1(k7_relat_1(sK2,X1),k3_xboole_0(X1,k10_relat_1(sK2,X2)))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f146,f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ( ! [X8,X7] : (k10_relat_1(k7_relat_1(sK2,X7),X8) = k3_xboole_0(X7,k10_relat_1(sK2,X8))) )),
% 0.22/0.57    inference(resolution,[],[f30,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.22/0.57  fof(f146,plain,(
% 0.22/0.57    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k3_xboole_0(X2,k9_relat_1(sK2,X1))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f145,f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ( ! [X2] : (v1_relat_1(k7_relat_1(sK2,X2))) )),
% 0.22/0.57    inference(resolution,[],[f30,f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.57  fof(f145,plain,(
% 0.22/0.57    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k3_xboole_0(X2,k9_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X1))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f141,f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X1] : (v1_funct_1(k7_relat_1(sK2,X1))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f59,f30])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X1] : (v1_funct_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 0.22/0.57    inference(resolution,[],[f31,f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    v1_funct_1(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f141,plain,(
% 0.22/0.57    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k3_xboole_0(X2,k9_relat_1(sK2,X1)) | ~v1_funct_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X1))) )),
% 0.22/0.57    inference(superposition,[],[f40,f137])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f63,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X3] : (k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)) )),
% 0.22/0.57    inference(resolution,[],[f30,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 0.22/0.57    inference(resolution,[],[f52,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(flattening,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),
% 0.22/0.57    inference(forward_demodulation,[],[f32,f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (2060)------------------------------
% 0.22/0.57  % (2060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (2060)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (2060)Memory used [KB]: 1791
% 0.22/0.57  % (2060)Time elapsed: 0.118 s
% 0.22/0.57  % (2060)------------------------------
% 0.22/0.57  % (2060)------------------------------
% 0.22/0.57  % (2051)Success in time 0.202 s
%------------------------------------------------------------------------------
