%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:05 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 123 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 197 expanded)
%              Number of equality atoms :   30 (  78 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(resolution,[],[f522,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f522,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))) ),
    inference(forward_demodulation,[],[f500,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f500,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))) ),
    inference(resolution,[],[f193,f59])).

fof(f59,plain,(
    ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))) ),
    inference(backward_demodulation,[],[f47,f55])).

fof(f55,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f39,f23])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_funct_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f47,plain,(
    ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))) ),
    inference(backward_demodulation,[],[f37,f41])).

fof(f37,plain,(
    ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))) ),
    inference(definition_unfolding,[],[f24,f36,f36])).

fof(f24,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f193,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,X8),X9),X10)
      | ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X8),k9_relat_1(sK2,X8),X9))),X10) ) ),
    inference(superposition,[],[f75,f123])).

fof(f123,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),X1))) ),
    inference(forward_demodulation,[],[f121,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f29,f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f121,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k2_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(k7_relat_1(sK2,X0)),X1))) ),
    inference(resolution,[],[f58,f23])).

fof(f58,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(k7_relat_1(X1,X2),X3) = k10_relat_1(k7_relat_1(X1,X2),k1_setfam_1(k1_enumset1(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(k7_relat_1(X1,X2)),X3))) ) ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
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

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,X0),X1),X2)
      | ~ r1_tarski(k10_relat_1(sK2,X1),X2) ) ),
    inference(superposition,[],[f53,f55])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f38,f41])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:13:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.18/0.52  % (10908)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.18/0.53  % (10926)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.18/0.53  % (10917)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.18/0.53  % (10914)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.18/0.53  % (10924)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.18/0.54  % (10906)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.18/0.54  % (10910)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.18/0.54  % (10907)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.18/0.54  % (10933)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.18/0.54  % (10934)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.18/0.54  % (10909)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.41/0.54  % (10934)Refutation not found, incomplete strategy% (10934)------------------------------
% 1.41/0.54  % (10934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (10913)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.41/0.54  % (10935)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.54  % (10934)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (10934)Memory used [KB]: 10746
% 1.41/0.54  % (10934)Time elapsed: 0.119 s
% 1.41/0.54  % (10934)------------------------------
% 1.41/0.54  % (10934)------------------------------
% 1.41/0.54  % (10922)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.54  % (10935)Refutation not found, incomplete strategy% (10935)------------------------------
% 1.41/0.54  % (10935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (10935)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (10935)Memory used [KB]: 1663
% 1.41/0.54  % (10935)Time elapsed: 0.127 s
% 1.41/0.54  % (10935)------------------------------
% 1.41/0.54  % (10935)------------------------------
% 1.41/0.54  % (10928)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.41/0.55  % (10922)Refutation not found, incomplete strategy% (10922)------------------------------
% 1.41/0.55  % (10922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (10922)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (10922)Memory used [KB]: 10618
% 1.41/0.55  % (10922)Time elapsed: 0.129 s
% 1.41/0.55  % (10922)------------------------------
% 1.41/0.55  % (10922)------------------------------
% 1.41/0.55  % (10930)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.55  % (10911)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.41/0.55  % (10921)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.55  % (10920)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.55  % (10918)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.41/0.55  % (10920)Refutation not found, incomplete strategy% (10920)------------------------------
% 1.41/0.55  % (10920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (10915)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.55  % (10925)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.55  % (10912)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  % (10932)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (10931)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.41/0.56  % (10916)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.56  % (10927)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.41/0.56  % (10924)Refutation not found, incomplete strategy% (10924)------------------------------
% 1.41/0.56  % (10924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (10924)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (10924)Memory used [KB]: 1663
% 1.41/0.56  % (10924)Time elapsed: 0.135 s
% 1.41/0.56  % (10924)------------------------------
% 1.41/0.56  % (10924)------------------------------
% 1.41/0.56  % (10916)Refutation not found, incomplete strategy% (10916)------------------------------
% 1.41/0.56  % (10916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (10916)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (10916)Memory used [KB]: 10746
% 1.41/0.56  % (10916)Time elapsed: 0.139 s
% 1.41/0.56  % (10916)------------------------------
% 1.41/0.56  % (10916)------------------------------
% 1.41/0.56  % (10923)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.56  % (10929)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.56  % (10933)Refutation not found, incomplete strategy% (10933)------------------------------
% 1.41/0.56  % (10933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (10919)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.56  % (10933)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (10933)Memory used [KB]: 6140
% 1.41/0.56  % (10933)Time elapsed: 0.140 s
% 1.41/0.56  % (10933)------------------------------
% 1.41/0.56  % (10933)------------------------------
% 1.41/0.57  % (10920)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (10920)Memory used [KB]: 1663
% 1.41/0.57  % (10920)Time elapsed: 0.089 s
% 1.41/0.57  % (10920)------------------------------
% 1.41/0.57  % (10920)------------------------------
% 1.41/0.57  % (10911)Refutation found. Thanks to Tanya!
% 1.41/0.57  % SZS status Theorem for theBenchmark
% 1.41/0.59  % SZS output start Proof for theBenchmark
% 1.41/0.59  fof(f528,plain,(
% 1.41/0.59    $false),
% 1.41/0.59    inference(resolution,[],[f522,f42])).
% 1.41/0.59  fof(f42,plain,(
% 1.41/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.59    inference(equality_resolution,[],[f27])).
% 1.41/0.59  fof(f27,plain,(
% 1.41/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.41/0.59    inference(cnf_transformation,[],[f22])).
% 1.41/0.59  fof(f22,plain,(
% 1.41/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.59    inference(flattening,[],[f21])).
% 1.41/0.59  fof(f21,plain,(
% 1.41/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.59    inference(nnf_transformation,[],[f1])).
% 1.41/0.59  fof(f1,axiom,(
% 1.41/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.59  fof(f522,plain,(
% 1.41/0.59    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))))),
% 1.41/0.59    inference(forward_demodulation,[],[f500,f41])).
% 1.41/0.59  fof(f41,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.41/0.59    inference(definition_unfolding,[],[f33,f35,f35])).
% 1.41/0.59  fof(f35,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f4])).
% 1.41/0.59  fof(f4,axiom,(
% 1.41/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.59  fof(f33,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f3])).
% 1.41/0.59  fof(f3,axiom,(
% 1.41/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.41/0.59  fof(f500,plain,(
% 1.41/0.59    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))))),
% 1.41/0.59    inference(resolution,[],[f193,f59])).
% 1.41/0.59  fof(f59,plain,(
% 1.41/0.59    ~r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))))),
% 1.41/0.59    inference(backward_demodulation,[],[f47,f55])).
% 1.41/0.59  fof(f55,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))) )),
% 1.41/0.59    inference(resolution,[],[f39,f23])).
% 1.41/0.59  fof(f23,plain,(
% 1.41/0.59    v1_relat_1(sK2)),
% 1.41/0.59    inference(cnf_transformation,[],[f20])).
% 1.41/0.59  fof(f20,plain,(
% 1.41/0.59    ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1))) & v1_relat_1(sK2)),
% 1.41/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).
% 1.41/0.59  fof(f19,plain,(
% 1.41/0.59    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) & v1_relat_1(X2)) => (~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1))) & v1_relat_1(sK2))),
% 1.41/0.59    introduced(choice_axiom,[])).
% 1.41/0.59  fof(f13,plain,(
% 1.41/0.59    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) & v1_relat_1(X2))),
% 1.41/0.59    inference(ennf_transformation,[],[f12])).
% 1.41/0.59  fof(f12,negated_conjecture,(
% 1.41/0.59    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))))),
% 1.41/0.59    inference(negated_conjecture,[],[f11])).
% 1.41/0.59  fof(f11,conjecture,(
% 1.41/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))))),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_funct_1)).
% 1.41/0.59  fof(f39,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 1.41/0.59    inference(definition_unfolding,[],[f30,f36])).
% 1.41/0.59  fof(f36,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.41/0.59    inference(definition_unfolding,[],[f34,f35])).
% 1.41/0.59  fof(f34,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f6])).
% 1.41/0.59  fof(f6,axiom,(
% 1.41/0.59    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.41/0.59  fof(f30,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f16])).
% 1.41/0.59  fof(f16,plain,(
% 1.41/0.59    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.41/0.59    inference(ennf_transformation,[],[f10])).
% 1.41/0.59  fof(f10,axiom,(
% 1.41/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.41/0.59  fof(f47,plain,(
% 1.41/0.59    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))))),
% 1.41/0.59    inference(backward_demodulation,[],[f37,f41])).
% 1.41/0.59  fof(f37,plain,(
% 1.41/0.59    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))))),
% 1.41/0.59    inference(definition_unfolding,[],[f24,f36,f36])).
% 1.41/0.59  fof(f24,plain,(
% 1.41/0.59    ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1)))),
% 1.41/0.59    inference(cnf_transformation,[],[f20])).
% 1.41/0.59  fof(f193,plain,(
% 1.41/0.59    ( ! [X10,X8,X9] : (r1_tarski(k10_relat_1(k7_relat_1(sK2,X8),X9),X10) | ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X8),k9_relat_1(sK2,X8),X9))),X10)) )),
% 1.41/0.59    inference(superposition,[],[f75,f123])).
% 1.41/0.59  fof(f123,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),X1)))) )),
% 1.41/0.59    inference(forward_demodulation,[],[f121,f48])).
% 1.41/0.59  fof(f48,plain,(
% 1.41/0.59    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 1.41/0.59    inference(resolution,[],[f29,f23])).
% 1.41/0.59  fof(f29,plain,(
% 1.41/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f15])).
% 1.41/0.59  fof(f15,plain,(
% 1.41/0.59    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.41/0.59    inference(ennf_transformation,[],[f8])).
% 1.41/0.59  fof(f8,axiom,(
% 1.41/0.59    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.41/0.59  fof(f121,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k2_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(k7_relat_1(sK2,X0)),X1)))) )),
% 1.41/0.59    inference(resolution,[],[f58,f23])).
% 1.41/0.59  fof(f58,plain,(
% 1.41/0.59    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k10_relat_1(k7_relat_1(X1,X2),X3) = k10_relat_1(k7_relat_1(X1,X2),k1_setfam_1(k1_enumset1(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(k7_relat_1(X1,X2)),X3)))) )),
% 1.41/0.59    inference(resolution,[],[f40,f32])).
% 1.41/0.59  fof(f32,plain,(
% 1.41/0.59    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f18])).
% 1.41/0.59  fof(f18,plain,(
% 1.41/0.59    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.41/0.59    inference(ennf_transformation,[],[f7])).
% 1.41/0.59  fof(f7,axiom,(
% 1.41/0.59    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.41/0.59  fof(f40,plain,(
% 1.41/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0)))) )),
% 1.41/0.59    inference(definition_unfolding,[],[f31,f36])).
% 1.41/0.59  fof(f31,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f17])).
% 1.41/0.59  fof(f17,plain,(
% 1.41/0.59    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.41/0.59    inference(ennf_transformation,[],[f9])).
% 1.41/0.59  fof(f9,axiom,(
% 1.41/0.59    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 1.41/0.59  fof(f75,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK2,X0),X1),X2) | ~r1_tarski(k10_relat_1(sK2,X1),X2)) )),
% 1.41/0.59    inference(superposition,[],[f53,f55])).
% 1.41/0.59  fof(f53,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X2) | ~r1_tarski(X0,X2)) )),
% 1.41/0.59    inference(superposition,[],[f38,f41])).
% 1.41/0.59  fof(f38,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 1.41/0.59    inference(definition_unfolding,[],[f25,f36])).
% 1.41/0.59  fof(f25,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f14])).
% 1.41/0.59  fof(f14,plain,(
% 1.41/0.59    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.41/0.59    inference(ennf_transformation,[],[f2])).
% 1.41/0.59  fof(f2,axiom,(
% 1.41/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.41/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.41/0.59  % SZS output end Proof for theBenchmark
% 1.41/0.59  % (10911)------------------------------
% 1.41/0.59  % (10911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.59  % (10911)Termination reason: Refutation
% 1.41/0.59  
% 1.41/0.59  % (10911)Memory used [KB]: 2174
% 1.41/0.59  % (10911)Time elapsed: 0.160 s
% 1.41/0.59  % (10911)------------------------------
% 1.41/0.59  % (10911)------------------------------
% 1.41/0.59  % (10905)Success in time 0.224 s
%------------------------------------------------------------------------------
