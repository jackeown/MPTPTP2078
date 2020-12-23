%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:49 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   55 (  90 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  111 ( 215 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f924,plain,(
    $false ),
    inference(subsumption_resolution,[],[f923,f42])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f38])).

fof(f38,plain,
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

fof(f923,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f921,f43])).

fof(f43,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f921,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f911,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f911,plain,(
    ! [X0] : ~ r1_tarski(sK0,k10_relat_1(sK1,X0)) ),
    inference(subsumption_resolution,[],[f909,f42])).

fof(f909,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r1_tarski(sK0,k10_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f908,f203])).

fof(f203,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(X3,k1_relat_1(k7_relat_1(X4,X3)))
      | ~ v1_relat_1(X4)
      | ~ r1_tarski(X3,k10_relat_1(X4,X5)) ) ),
    inference(superposition,[],[f153,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f153,plain,(
    ! [X12,X13,X11] :
      ( r1_tarski(k3_xboole_0(X12,k10_relat_1(X11,X13)),k1_relat_1(k7_relat_1(X11,X12)))
      | ~ v1_relat_1(X11) ) ),
    inference(subsumption_resolution,[],[f146,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f146,plain,(
    ! [X12,X13,X11] :
      ( r1_tarski(k3_xboole_0(X12,k10_relat_1(X11,X13)),k1_relat_1(k7_relat_1(X11,X12)))
      | ~ v1_relat_1(k7_relat_1(X11,X12))
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f51,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f51,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f908,plain,(
    ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f870,f42])).

fof(f870,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f127,f252])).

fof(f252,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,k10_relat_1(X2,k9_relat_1(X2,X3))) = k1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,k10_relat_1(X2,k9_relat_1(X2,X3))) = k1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f106,f60])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f105,f50])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f127,plain,(
    ! [X3] : ~ r1_tarski(sK0,k3_xboole_0(X3,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) ),
    inference(resolution,[],[f120,f67])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f120,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      | ~ r1_tarski(sK0,X8) ) ),
    inference(resolution,[],[f82,f44])).

fof(f44,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f63,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:22:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (26625)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (26631)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (26634)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (26644)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (26627)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (26624)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (26640)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (26646)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (26626)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (26640)Refutation not found, incomplete strategy% (26640)------------------------------
% 0.21/0.52  % (26640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26640)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26640)Memory used [KB]: 10618
% 0.21/0.52  % (26640)Time elapsed: 0.116 s
% 0.21/0.52  % (26640)------------------------------
% 0.21/0.52  % (26640)------------------------------
% 0.21/0.53  % (26638)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (26642)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (26639)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (26629)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (26628)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (26635)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (26650)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (26633)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (26632)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (26648)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (26649)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (26651)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (26634)Refutation not found, incomplete strategy% (26634)------------------------------
% 0.21/0.53  % (26634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26634)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26634)Memory used [KB]: 10746
% 0.21/0.53  % (26634)Time elapsed: 0.126 s
% 0.21/0.53  % (26634)------------------------------
% 0.21/0.53  % (26634)------------------------------
% 0.21/0.54  % (26653)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (26653)Refutation not found, incomplete strategy% (26653)------------------------------
% 0.21/0.54  % (26653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26653)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26653)Memory used [KB]: 1663
% 0.21/0.54  % (26653)Time elapsed: 0.003 s
% 0.21/0.54  % (26653)------------------------------
% 0.21/0.54  % (26653)------------------------------
% 0.21/0.54  % (26645)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (26652)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (26630)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (26652)Refutation not found, incomplete strategy% (26652)------------------------------
% 0.21/0.54  % (26652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26652)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26652)Memory used [KB]: 10746
% 0.21/0.54  % (26652)Time elapsed: 0.136 s
% 0.21/0.54  % (26652)------------------------------
% 0.21/0.54  % (26652)------------------------------
% 0.21/0.54  % (26636)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (26643)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (26647)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (26641)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (26637)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.87/0.61  % (26633)Refutation found. Thanks to Tanya!
% 1.87/0.61  % SZS status Theorem for theBenchmark
% 1.87/0.61  % SZS output start Proof for theBenchmark
% 1.87/0.61  fof(f924,plain,(
% 1.87/0.61    $false),
% 1.87/0.61    inference(subsumption_resolution,[],[f923,f42])).
% 1.87/0.61  fof(f42,plain,(
% 1.87/0.61    v1_relat_1(sK1)),
% 1.87/0.61    inference(cnf_transformation,[],[f39])).
% 1.87/0.61  fof(f39,plain,(
% 1.87/0.61    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f38])).
% 1.87/0.61  fof(f38,plain,(
% 1.87/0.61    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f22,plain,(
% 1.87/0.61    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.87/0.61    inference(flattening,[],[f21])).
% 1.87/0.61  fof(f21,plain,(
% 1.87/0.61    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.87/0.61    inference(ennf_transformation,[],[f20])).
% 1.87/0.61  fof(f20,negated_conjecture,(
% 1.87/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.87/0.61    inference(negated_conjecture,[],[f19])).
% 1.87/0.61  fof(f19,conjecture,(
% 1.87/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.87/0.61  fof(f923,plain,(
% 1.87/0.61    ~v1_relat_1(sK1)),
% 1.87/0.61    inference(subsumption_resolution,[],[f921,f43])).
% 1.87/0.61  fof(f43,plain,(
% 1.87/0.61    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.87/0.61    inference(cnf_transformation,[],[f39])).
% 1.87/0.61  fof(f921,plain,(
% 1.87/0.61    ~r1_tarski(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.87/0.61    inference(superposition,[],[f911,f45])).
% 1.87/0.61  fof(f45,plain,(
% 1.87/0.61    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f23])).
% 1.87/0.61  fof(f23,plain,(
% 1.87/0.61    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f14])).
% 1.87/0.61  fof(f14,axiom,(
% 1.87/0.61    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.87/0.61  fof(f911,plain,(
% 1.87/0.61    ( ! [X0] : (~r1_tarski(sK0,k10_relat_1(sK1,X0))) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f909,f42])).
% 1.87/0.61  fof(f909,plain,(
% 1.87/0.61    ( ! [X0] : (~v1_relat_1(sK1) | ~r1_tarski(sK0,k10_relat_1(sK1,X0))) )),
% 1.87/0.61    inference(resolution,[],[f908,f203])).
% 1.87/0.61  fof(f203,plain,(
% 1.87/0.61    ( ! [X4,X5,X3] : (r1_tarski(X3,k1_relat_1(k7_relat_1(X4,X3))) | ~v1_relat_1(X4) | ~r1_tarski(X3,k10_relat_1(X4,X5))) )),
% 1.87/0.61    inference(superposition,[],[f153,f56])).
% 1.87/0.61  fof(f56,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f30])).
% 1.87/0.61  fof(f30,plain,(
% 1.87/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.87/0.61    inference(ennf_transformation,[],[f7])).
% 1.87/0.61  fof(f7,axiom,(
% 1.87/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.87/0.61  fof(f153,plain,(
% 1.87/0.61    ( ! [X12,X13,X11] : (r1_tarski(k3_xboole_0(X12,k10_relat_1(X11,X13)),k1_relat_1(k7_relat_1(X11,X12))) | ~v1_relat_1(X11)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f146,f50])).
% 1.87/0.61  fof(f50,plain,(
% 1.87/0.61    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f24])).
% 1.87/0.61  fof(f24,plain,(
% 1.87/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f11])).
% 1.87/0.61  fof(f11,axiom,(
% 1.87/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.87/0.61  fof(f146,plain,(
% 1.87/0.61    ( ! [X12,X13,X11] : (r1_tarski(k3_xboole_0(X12,k10_relat_1(X11,X13)),k1_relat_1(k7_relat_1(X11,X12))) | ~v1_relat_1(k7_relat_1(X11,X12)) | ~v1_relat_1(X11)) )),
% 1.87/0.61    inference(superposition,[],[f51,f60])).
% 1.87/0.61  fof(f60,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f31])).
% 1.87/0.61  fof(f31,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.87/0.61    inference(ennf_transformation,[],[f18])).
% 1.87/0.61  fof(f18,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.87/0.61  fof(f51,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f25])).
% 1.87/0.61  fof(f25,plain,(
% 1.87/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.87/0.61    inference(ennf_transformation,[],[f13])).
% 1.87/0.61  fof(f13,axiom,(
% 1.87/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.87/0.61  fof(f908,plain,(
% 1.87/0.61    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.87/0.61    inference(subsumption_resolution,[],[f870,f42])).
% 1.87/0.61  fof(f870,plain,(
% 1.87/0.61    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 1.87/0.61    inference(superposition,[],[f127,f252])).
% 1.87/0.61  fof(f252,plain,(
% 1.87/0.61    ( ! [X2,X3] : (k3_xboole_0(X3,k10_relat_1(X2,k9_relat_1(X2,X3))) = k1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2)) )),
% 1.87/0.61    inference(duplicate_literal_removal,[],[f242])).
% 1.87/0.61  fof(f242,plain,(
% 1.87/0.61    ( ! [X2,X3] : (k3_xboole_0(X3,k10_relat_1(X2,k9_relat_1(X2,X3))) = k1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2) | ~v1_relat_1(X2)) )),
% 1.87/0.61    inference(superposition,[],[f106,f60])).
% 1.87/0.61  fof(f106,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f105,f50])).
% 1.87/0.61  fof(f105,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.87/0.61    inference(superposition,[],[f45,f53])).
% 1.87/0.61  fof(f53,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f27])).
% 1.87/0.61  fof(f27,plain,(
% 1.87/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.87/0.61    inference(ennf_transformation,[],[f12])).
% 1.87/0.61  fof(f12,axiom,(
% 1.87/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.87/0.61  fof(f127,plain,(
% 1.87/0.61    ( ! [X3] : (~r1_tarski(sK0,k3_xboole_0(X3,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) )),
% 1.87/0.61    inference(resolution,[],[f120,f67])).
% 1.87/0.61  fof(f67,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.87/0.61    inference(superposition,[],[f47,f48])).
% 1.87/0.61  fof(f48,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f1])).
% 1.87/0.61  fof(f1,axiom,(
% 1.87/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.87/0.61  fof(f47,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f6])).
% 1.87/0.61  fof(f6,axiom,(
% 1.87/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.87/0.61  fof(f120,plain,(
% 1.87/0.61    ( ! [X8] : (~r1_tarski(X8,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~r1_tarski(sK0,X8)) )),
% 1.87/0.61    inference(resolution,[],[f82,f44])).
% 1.87/0.61  fof(f44,plain,(
% 1.87/0.61    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.87/0.61    inference(cnf_transformation,[],[f39])).
% 1.87/0.61  fof(f82,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.87/0.61    inference(superposition,[],[f63,f55])).
% 1.87/0.61  fof(f55,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f29])).
% 1.87/0.61  fof(f29,plain,(
% 1.87/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.87/0.61    inference(ennf_transformation,[],[f5])).
% 1.87/0.61  fof(f5,axiom,(
% 1.87/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.87/0.61  fof(f63,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f35])).
% 1.87/0.61  fof(f35,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.87/0.61    inference(ennf_transformation,[],[f4])).
% 1.87/0.61  fof(f4,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.87/0.61  % SZS output end Proof for theBenchmark
% 1.87/0.61  % (26633)------------------------------
% 1.87/0.61  % (26633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (26633)Termination reason: Refutation
% 1.87/0.61  
% 1.87/0.61  % (26633)Memory used [KB]: 2302
% 1.87/0.61  % (26633)Time elapsed: 0.197 s
% 1.87/0.61  % (26633)------------------------------
% 1.87/0.61  % (26633)------------------------------
% 1.87/0.62  % (26623)Success in time 0.259 s
%------------------------------------------------------------------------------
