%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:46 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   56 (  93 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   15
%              Number of atoms          :  112 ( 218 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(subsumption_resolution,[],[f259,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f259,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f258,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f258,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f247,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f247,plain,(
    ! [X0] : ~ r1_tarski(sK0,k10_relat_1(sK1,X0)) ),
    inference(subsumption_resolution,[],[f245,f30])).

fof(f245,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r1_tarski(sK0,k10_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f244,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_relat_1(k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k10_relat_1(X1,X2)) ) ),
    inference(superposition,[],[f78,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,k10_relat_1(X0,X2)),k1_relat_1(k7_relat_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f75,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,k10_relat_1(X0,X2)),k1_relat_1(k7_relat_1(X0,X1)))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f38,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f244,plain,(
    ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f227,f30])).

fof(f227,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f148,f121])).

fof(f121,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,k10_relat_1(X2,k9_relat_1(X2,X3))) = k1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,k10_relat_1(X2,k9_relat_1(X2,X3))) = k1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f71,f45])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f70,f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f148,plain,(
    ! [X15] : ~ r1_tarski(sK0,k3_xboole_0(X15,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) ),
    inference(superposition,[],[f68,f56])).

fof(f56,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f49,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f68,plain,(
    ! [X2] : ~ r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X2)) ),
    inference(resolution,[],[f63,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (10253)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (10245)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (10242)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (10237)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (10243)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (10244)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (10258)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (10250)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (10234)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (10231)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (10259)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (10240)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (10233)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (10260)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (10232)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (10236)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (10251)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (10246)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (10257)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (10235)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.26/0.54  % (10256)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.26/0.54  % (10255)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.26/0.54  % (10241)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.26/0.54  % (10254)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.26/0.54  % (10252)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.26/0.54  % (10248)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.26/0.54  % (10249)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.26/0.54  % (10247)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.26/0.54  % (10238)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.26/0.55  % (10239)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.26/0.55  % (10240)Refutation found. Thanks to Tanya!
% 1.26/0.55  % SZS status Theorem for theBenchmark
% 1.26/0.55  % SZS output start Proof for theBenchmark
% 1.26/0.55  fof(f260,plain,(
% 1.26/0.55    $false),
% 1.26/0.55    inference(subsumption_resolution,[],[f259,f30])).
% 1.26/0.55  fof(f30,plain,(
% 1.26/0.55    v1_relat_1(sK1)),
% 1.26/0.55    inference(cnf_transformation,[],[f27])).
% 1.26/0.55  fof(f27,plain,(
% 1.26/0.55    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.26/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26])).
% 1.26/0.55  fof(f26,plain,(
% 1.26/0.55    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.26/0.55    introduced(choice_axiom,[])).
% 1.26/0.55  fof(f16,plain,(
% 1.26/0.55    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.26/0.55    inference(flattening,[],[f15])).
% 1.26/0.55  fof(f15,plain,(
% 1.26/0.55    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.26/0.55    inference(ennf_transformation,[],[f14])).
% 1.26/0.55  fof(f14,negated_conjecture,(
% 1.26/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.26/0.55    inference(negated_conjecture,[],[f13])).
% 1.26/0.55  fof(f13,conjecture,(
% 1.26/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.26/0.55  fof(f259,plain,(
% 1.26/0.55    ~v1_relat_1(sK1)),
% 1.26/0.55    inference(subsumption_resolution,[],[f258,f31])).
% 1.26/0.55  fof(f31,plain,(
% 1.26/0.55    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.26/0.55    inference(cnf_transformation,[],[f27])).
% 1.26/0.55  fof(f258,plain,(
% 1.26/0.55    ~r1_tarski(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.26/0.55    inference(superposition,[],[f247,f33])).
% 1.26/0.55  fof(f33,plain,(
% 1.26/0.55    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.26/0.55    inference(cnf_transformation,[],[f17])).
% 1.26/0.55  fof(f17,plain,(
% 1.26/0.55    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.55    inference(ennf_transformation,[],[f10])).
% 1.26/0.55  fof(f10,axiom,(
% 1.26/0.55    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.26/0.55  fof(f247,plain,(
% 1.26/0.55    ( ! [X0] : (~r1_tarski(sK0,k10_relat_1(sK1,X0))) )),
% 1.26/0.55    inference(subsumption_resolution,[],[f245,f30])).
% 1.26/0.55  fof(f245,plain,(
% 1.26/0.55    ( ! [X0] : (~v1_relat_1(sK1) | ~r1_tarski(sK0,k10_relat_1(sK1,X0))) )),
% 1.26/0.55    inference(resolution,[],[f244,f96])).
% 1.26/0.55  fof(f96,plain,(
% 1.26/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_relat_1(k7_relat_1(X1,X0))) | ~v1_relat_1(X1) | ~r1_tarski(X0,k10_relat_1(X1,X2))) )),
% 1.26/0.55    inference(superposition,[],[f78,f41])).
% 1.26/0.55  fof(f41,plain,(
% 1.26/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.26/0.55    inference(cnf_transformation,[],[f22])).
% 1.26/0.55  fof(f22,plain,(
% 1.26/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.26/0.55    inference(ennf_transformation,[],[f4])).
% 1.26/0.55  fof(f4,axiom,(
% 1.26/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.26/0.55  fof(f78,plain,(
% 1.26/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,k10_relat_1(X0,X2)),k1_relat_1(k7_relat_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 1.26/0.55    inference(subsumption_resolution,[],[f75,f37])).
% 1.26/0.55  fof(f37,plain,(
% 1.26/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.26/0.55    inference(cnf_transformation,[],[f18])).
% 1.26/0.55  fof(f18,plain,(
% 1.26/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.26/0.55    inference(ennf_transformation,[],[f7])).
% 1.26/0.55  fof(f7,axiom,(
% 1.26/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.26/0.55  fof(f75,plain,(
% 1.26/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,k10_relat_1(X0,X2)),k1_relat_1(k7_relat_1(X0,X1))) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.26/0.55    inference(superposition,[],[f38,f45])).
% 1.26/0.55  fof(f45,plain,(
% 1.26/0.55    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.26/0.55    inference(cnf_transformation,[],[f23])).
% 1.26/0.55  fof(f23,plain,(
% 1.26/0.55    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.26/0.55    inference(ennf_transformation,[],[f12])).
% 1.26/0.55  fof(f12,axiom,(
% 1.26/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.26/0.55  fof(f38,plain,(
% 1.26/0.55    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.26/0.55    inference(cnf_transformation,[],[f19])).
% 1.26/0.55  fof(f19,plain,(
% 1.26/0.55    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.26/0.55    inference(ennf_transformation,[],[f9])).
% 1.26/0.55  fof(f9,axiom,(
% 1.26/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.26/0.55  fof(f244,plain,(
% 1.26/0.55    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.26/0.55    inference(subsumption_resolution,[],[f227,f30])).
% 1.26/0.55  fof(f227,plain,(
% 1.26/0.55    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 1.26/0.55    inference(superposition,[],[f148,f121])).
% 1.26/0.55  fof(f121,plain,(
% 1.26/0.55    ( ! [X2,X3] : (k3_xboole_0(X3,k10_relat_1(X2,k9_relat_1(X2,X3))) = k1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2)) )),
% 1.26/0.55    inference(duplicate_literal_removal,[],[f115])).
% 1.26/0.55  fof(f115,plain,(
% 1.26/0.55    ( ! [X2,X3] : (k3_xboole_0(X3,k10_relat_1(X2,k9_relat_1(X2,X3))) = k1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2) | ~v1_relat_1(X2)) )),
% 1.26/0.55    inference(superposition,[],[f71,f45])).
% 1.26/0.55  fof(f71,plain,(
% 1.26/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.26/0.55    inference(subsumption_resolution,[],[f70,f37])).
% 1.26/0.55  fof(f70,plain,(
% 1.26/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.26/0.55    inference(superposition,[],[f33,f40])).
% 1.26/0.55  fof(f40,plain,(
% 1.26/0.55    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.26/0.55    inference(cnf_transformation,[],[f21])).
% 1.26/0.55  fof(f21,plain,(
% 1.26/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.26/0.55    inference(ennf_transformation,[],[f8])).
% 1.26/0.55  fof(f8,axiom,(
% 1.26/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.26/0.55  fof(f148,plain,(
% 1.26/0.55    ( ! [X15] : (~r1_tarski(sK0,k3_xboole_0(X15,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) )),
% 1.26/0.55    inference(superposition,[],[f68,f56])).
% 1.26/0.55  fof(f56,plain,(
% 1.26/0.55    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.26/0.55    inference(superposition,[],[f49,f36])).
% 1.26/0.55  fof(f36,plain,(
% 1.26/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.26/0.55    inference(cnf_transformation,[],[f6])).
% 1.26/0.55  fof(f6,axiom,(
% 1.26/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.26/0.55  fof(f49,plain,(
% 1.26/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.26/0.55    inference(superposition,[],[f36,f35])).
% 1.26/0.55  fof(f35,plain,(
% 1.26/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.26/0.55    inference(cnf_transformation,[],[f5])).
% 1.26/0.55  fof(f5,axiom,(
% 1.26/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.26/0.55  fof(f68,plain,(
% 1.26/0.55    ( ! [X2] : (~r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X2))) )),
% 1.26/0.55    inference(resolution,[],[f63,f34])).
% 1.26/0.55  fof(f34,plain,(
% 1.26/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.26/0.55    inference(cnf_transformation,[],[f2])).
% 1.26/0.55  fof(f2,axiom,(
% 1.26/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.26/0.55  fof(f63,plain,(
% 1.26/0.55    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~r1_tarski(sK0,X0)) )),
% 1.26/0.55    inference(resolution,[],[f46,f32])).
% 1.26/0.55  fof(f32,plain,(
% 1.26/0.55    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.26/0.55    inference(cnf_transformation,[],[f27])).
% 1.26/0.55  fof(f46,plain,(
% 1.26/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.26/0.55    inference(cnf_transformation,[],[f25])).
% 1.26/0.55  fof(f25,plain,(
% 1.26/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.26/0.55    inference(flattening,[],[f24])).
% 1.26/0.55  fof(f24,plain,(
% 1.26/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.26/0.55    inference(ennf_transformation,[],[f3])).
% 1.26/0.55  fof(f3,axiom,(
% 1.26/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.26/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.26/0.55  % SZS output end Proof for theBenchmark
% 1.26/0.55  % (10240)------------------------------
% 1.26/0.55  % (10240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (10240)Termination reason: Refutation
% 1.26/0.55  
% 1.26/0.55  % (10240)Memory used [KB]: 1918
% 1.26/0.55  % (10240)Time elapsed: 0.148 s
% 1.26/0.55  % (10240)------------------------------
% 1.26/0.55  % (10240)------------------------------
% 1.26/0.55  % (10230)Success in time 0.195 s
%------------------------------------------------------------------------------
