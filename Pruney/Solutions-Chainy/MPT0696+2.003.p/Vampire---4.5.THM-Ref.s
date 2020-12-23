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
% DateTime   : Thu Dec  3 12:54:05 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 123 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 194 expanded)
%              Number of equality atoms :   32 (  80 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(resolution,[],[f218,f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f218,plain,(
    ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(superposition,[],[f72,f160])).

fof(f160,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))) ),
    inference(superposition,[],[f129,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f129,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),X1))) ),
    inference(forward_demodulation,[],[f127,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f29,f23])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f127,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k2_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(k7_relat_1(sK2,X0)),X1))) ),
    inference(resolution,[],[f64,f23])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f72,plain,(
    ! [X0] : ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))) ),
    inference(forward_demodulation,[],[f58,f56])).

fof(f56,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X1),k10_relat_1(sK2,X1),X0)) ),
    inference(superposition,[],[f53,f41])).

fof(f53,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f39,f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f30,f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f58,plain,(
    ! [X0] : ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k1_setfam_1(k1_enumset1(k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),X0))) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f55,plain,(
    ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))) ),
    inference(backward_demodulation,[],[f47,f53])).

fof(f47,plain,(
    ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))) ),
    inference(backward_demodulation,[],[f37,f41])).

fof(f37,plain,(
    ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))) ),
    inference(definition_unfolding,[],[f24,f36,f36])).

fof(f24,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (18666)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (18668)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (18681)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (18690)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (18670)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (18675)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (18673)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.28/0.52  % (18687)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.28/0.52  % (18692)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.28/0.53  % (18677)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.28/0.53  % (18678)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.28/0.53  % (18669)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.53  % (18683)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.54  % (18685)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.28/0.54  % (18696)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.54  % (18695)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.28/0.54  % (18671)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.39/0.54  % (18676)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.54  % (18694)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.54  % (18686)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.54  % (18672)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.54  % (18667)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.54  % (18688)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.39/0.54  % (18691)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.54  % (18676)Refutation not found, incomplete strategy% (18676)------------------------------
% 1.39/0.54  % (18676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (18676)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (18676)Memory used [KB]: 10746
% 1.39/0.54  % (18676)Time elapsed: 0.134 s
% 1.39/0.54  % (18676)------------------------------
% 1.39/0.54  % (18676)------------------------------
% 1.39/0.55  % (18674)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.55  % (18671)Refutation found. Thanks to Tanya!
% 1.39/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f226,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(resolution,[],[f218,f42])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f27])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f22])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(flattening,[],[f21])).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.55  fof(f218,plain,(
% 1.39/0.55    ~r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 1.39/0.55    inference(superposition,[],[f72,f160])).
% 1.39/0.55  fof(f160,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0))))) )),
% 1.39/0.55    inference(superposition,[],[f129,f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.39/0.55    inference(definition_unfolding,[],[f33,f35,f35])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f4])).
% 1.39/0.55  fof(f4,axiom,(
% 1.39/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.39/0.55  fof(f129,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),X1)))) )),
% 1.39/0.55    inference(forward_demodulation,[],[f127,f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 1.39/0.55    inference(resolution,[],[f29,f23])).
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    v1_relat_1(sK2)),
% 1.39/0.55    inference(cnf_transformation,[],[f20])).
% 1.39/0.55  fof(f20,plain,(
% 1.39/0.55    ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1))) & v1_relat_1(sK2)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).
% 1.39/0.55  fof(f19,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) & v1_relat_1(X2)) => (~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1))) & v1_relat_1(sK2))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f13,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) & v1_relat_1(X2))),
% 1.39/0.55    inference(ennf_transformation,[],[f12])).
% 1.39/0.55  fof(f12,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))))),
% 1.39/0.55    inference(negated_conjecture,[],[f11])).
% 1.39/0.55  fof(f11,conjecture,(
% 1.39/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_funct_1)).
% 1.39/0.55  fof(f29,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f15])).
% 1.39/0.55  fof(f15,plain,(
% 1.39/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.39/0.55    inference(ennf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,axiom,(
% 1.39/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.39/0.55  fof(f127,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(k2_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(k7_relat_1(sK2,X0)),X1)))) )),
% 1.39/0.55    inference(resolution,[],[f64,f23])).
% 1.39/0.55  fof(f64,plain,(
% 1.39/0.55    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k10_relat_1(k7_relat_1(X1,X2),X3) = k10_relat_1(k7_relat_1(X1,X2),k1_setfam_1(k1_enumset1(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(k7_relat_1(X1,X2)),X3)))) )),
% 1.39/0.55    inference(resolution,[],[f40,f32])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f18])).
% 1.39/0.55  fof(f18,plain,(
% 1.39/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.39/0.55  fof(f40,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0)))) )),
% 1.39/0.55    inference(definition_unfolding,[],[f31,f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.39/0.55    inference(definition_unfolding,[],[f34,f35])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f6])).
% 1.39/0.55  fof(f6,axiom,(
% 1.39/0.55    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f17])).
% 1.39/0.55  fof(f17,plain,(
% 1.39/0.55    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.39/0.55    inference(ennf_transformation,[],[f9])).
% 1.39/0.55  fof(f9,axiom,(
% 1.39/0.55    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.39/0.55  fof(f72,plain,(
% 1.39/0.55    ( ! [X0] : (~r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k10_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))))) )),
% 1.39/0.55    inference(forward_demodulation,[],[f58,f56])).
% 1.39/0.55  fof(f56,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X1),k10_relat_1(sK2,X1),X0))) )),
% 1.39/0.55    inference(superposition,[],[f53,f41])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))) )),
% 1.39/0.55    inference(resolution,[],[f39,f23])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 1.39/0.55    inference(definition_unfolding,[],[f30,f36])).
% 1.39/0.55  fof(f30,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f16])).
% 1.39/0.55  fof(f16,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.39/0.55  fof(f58,plain,(
% 1.39/0.55    ( ! [X0] : (~r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k1_setfam_1(k1_enumset1(k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),X0)))) )),
% 1.39/0.55    inference(resolution,[],[f55,f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) )),
% 1.39/0.55    inference(definition_unfolding,[],[f25,f36])).
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f14])).
% 1.39/0.55  fof(f14,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.39/0.55  fof(f55,plain,(
% 1.39/0.55    ~r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))))),
% 1.39/0.55    inference(backward_demodulation,[],[f47,f53])).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))))),
% 1.39/0.55    inference(backward_demodulation,[],[f37,f41])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))))),
% 1.39/0.55    inference(definition_unfolding,[],[f24,f36,f36])).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,sK0),sK1)))),
% 1.39/0.55    inference(cnf_transformation,[],[f20])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (18671)------------------------------
% 1.39/0.55  % (18671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (18671)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (18671)Memory used [KB]: 1918
% 1.39/0.55  % (18671)Time elapsed: 0.140 s
% 1.39/0.55  % (18671)------------------------------
% 1.39/0.55  % (18671)------------------------------
% 1.39/0.55  % (18679)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.55  % (18665)Success in time 0.191 s
%------------------------------------------------------------------------------
