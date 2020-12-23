%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:42 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 205 expanded)
%              Number of leaves         :   17 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 268 expanded)
%              Number of equality atoms :   52 ( 169 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(subsumption_resolution,[],[f471,f44])).

fof(f44,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f471,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f379,f243])).

fof(f243,plain,(
    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f238,f76])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f47,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f238,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0)) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(backward_demodulation,[],[f185,f231])).

fof(f231,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f225,f131])).

fof(f131,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f119,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f119,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f75,f81])).

fof(f81,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f56,f57,f57])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f46,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f225,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f146,f124])).

fof(f124,plain,(
    ! [X9] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X9,X9,k1_xboole_0)) ),
    inference(superposition,[],[f91,f81])).

fof(f146,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
    inference(backward_demodulation,[],[f82,f145])).

fof(f145,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7))) = k1_setfam_1(k1_enumset1(X6,X6,k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7))))) ),
    inference(forward_demodulation,[],[f141,f81])).

fof(f141,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7))) = k1_setfam_1(k1_enumset1(k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7))),k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7))),X6)) ),
    inference(resolution,[],[f84,f80])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))))) ),
    inference(definition_unfolding,[],[f60,f72,f73,f73])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f185,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f182,f81])).

fof(f182,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) ),
    inference(superposition,[],[f83,f144])).

fof(f144,plain,(
    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))))) ),
    inference(definition_unfolding,[],[f62,f74,f73,f74])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f379,plain,(
    ! [X6,X7] : r1_tarski(k10_relat_1(sK2,X6),k10_relat_1(sK2,k3_tarski(k1_enumset1(X6,X6,X7)))) ),
    inference(superposition,[],[f78,f199])).

fof(f199,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f69,f74,f74])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (2722)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (2713)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (2738)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (2723)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (2717)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (2711)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (2718)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (2731)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (2720)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (2715)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (2716)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (2726)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (2730)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (2734)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (2736)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (2727)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (2714)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (2712)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (2732)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (2709)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (2735)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (2710)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (2728)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (2729)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (2724)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (2733)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (2721)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (2725)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (2737)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.56  % (2719)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.71/0.58  % (2731)Refutation found. Thanks to Tanya!
% 1.71/0.58  % SZS status Theorem for theBenchmark
% 1.71/0.59  % SZS output start Proof for theBenchmark
% 1.71/0.59  fof(f474,plain,(
% 1.71/0.59    $false),
% 1.71/0.59    inference(subsumption_resolution,[],[f471,f44])).
% 1.71/0.59  fof(f44,plain,(
% 1.71/0.59    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.71/0.59    inference(cnf_transformation,[],[f38])).
% 1.71/0.59  fof(f38,plain,(
% 1.71/0.59    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.71/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f37])).
% 1.71/0.59  fof(f37,plain,(
% 1.71/0.59    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.71/0.59    introduced(choice_axiom,[])).
% 1.71/0.59  fof(f28,plain,(
% 1.71/0.59    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.71/0.59    inference(flattening,[],[f27])).
% 1.71/0.59  fof(f27,plain,(
% 1.71/0.59    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.71/0.59    inference(ennf_transformation,[],[f25])).
% 1.71/0.59  fof(f25,negated_conjecture,(
% 1.71/0.59    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.71/0.59    inference(negated_conjecture,[],[f24])).
% 1.71/0.59  fof(f24,conjecture,(
% 1.71/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 1.71/0.59  fof(f471,plain,(
% 1.71/0.59    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.71/0.59    inference(superposition,[],[f379,f243])).
% 1.71/0.59  fof(f243,plain,(
% 1.71/0.59    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.71/0.59    inference(forward_demodulation,[],[f238,f76])).
% 1.71/0.59  fof(f76,plain,(
% 1.71/0.59    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 1.71/0.59    inference(definition_unfolding,[],[f47,f74])).
% 1.71/0.59  fof(f74,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f59,f57])).
% 1.71/0.59  fof(f57,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f16])).
% 1.71/0.59  fof(f16,axiom,(
% 1.71/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.71/0.59  fof(f59,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f17])).
% 1.71/0.59  fof(f17,axiom,(
% 1.71/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.71/0.59  fof(f47,plain,(
% 1.71/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f5])).
% 1.71/0.59  fof(f5,axiom,(
% 1.71/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.71/0.59  fof(f238,plain,(
% 1.71/0.59    k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0)) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.71/0.59    inference(backward_demodulation,[],[f185,f231])).
% 1.71/0.59  fof(f231,plain,(
% 1.71/0.59    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 1.71/0.59    inference(forward_demodulation,[],[f225,f131])).
% 1.71/0.59  fof(f131,plain,(
% 1.71/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.71/0.59    inference(forward_demodulation,[],[f119,f91])).
% 1.71/0.59  fof(f91,plain,(
% 1.71/0.59    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) )),
% 1.71/0.59    inference(resolution,[],[f79,f51])).
% 1.71/0.59  fof(f51,plain,(
% 1.71/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f30])).
% 1.71/0.59  fof(f30,plain,(
% 1.71/0.59    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.71/0.59    inference(ennf_transformation,[],[f11])).
% 1.71/0.59  fof(f11,axiom,(
% 1.71/0.59    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.71/0.59  fof(f79,plain,(
% 1.71/0.59    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 1.71/0.59    inference(definition_unfolding,[],[f54,f72])).
% 1.71/0.59  fof(f72,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f58,f57])).
% 1.71/0.59  fof(f58,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f18])).
% 1.71/0.59  fof(f18,axiom,(
% 1.71/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.71/0.59  fof(f54,plain,(
% 1.71/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f4])).
% 1.71/0.59  fof(f4,axiom,(
% 1.71/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.71/0.59  fof(f119,plain,(
% 1.71/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) = X0) )),
% 1.71/0.59    inference(superposition,[],[f75,f81])).
% 1.71/0.59  fof(f81,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.71/0.59    inference(definition_unfolding,[],[f56,f57,f57])).
% 1.71/0.59  fof(f56,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f15])).
% 1.71/0.59  fof(f15,axiom,(
% 1.71/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.71/0.59  fof(f75,plain,(
% 1.71/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0) )),
% 1.71/0.59    inference(definition_unfolding,[],[f46,f73])).
% 1.71/0.59  fof(f73,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f61,f72])).
% 1.71/0.59  fof(f61,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f3])).
% 1.71/0.59  fof(f3,axiom,(
% 1.71/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.71/0.59  fof(f46,plain,(
% 1.71/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f10])).
% 1.71/0.59  fof(f10,axiom,(
% 1.71/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.71/0.59  fof(f225,plain,(
% 1.71/0.59    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X2,k1_xboole_0))) )),
% 1.71/0.59    inference(superposition,[],[f146,f124])).
% 1.71/0.59  fof(f124,plain,(
% 1.71/0.59    ( ! [X9] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X9,X9,k1_xboole_0))) )),
% 1.71/0.59    inference(superposition,[],[f91,f81])).
% 1.71/0.59  fof(f146,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))) )),
% 1.71/0.59    inference(backward_demodulation,[],[f82,f145])).
% 1.71/0.59  fof(f145,plain,(
% 1.71/0.59    ( ! [X6,X7] : (k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7))) = k1_setfam_1(k1_enumset1(X6,X6,k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7)))))) )),
% 1.71/0.59    inference(forward_demodulation,[],[f141,f81])).
% 1.71/0.59  fof(f141,plain,(
% 1.71/0.59    ( ! [X6,X7] : (k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7))) = k1_setfam_1(k1_enumset1(k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7))),k5_xboole_0(X6,k1_setfam_1(k1_enumset1(X6,X6,X7))),X6))) )),
% 1.71/0.59    inference(resolution,[],[f84,f80])).
% 1.71/0.60  fof(f80,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X0)) )),
% 1.71/0.60    inference(definition_unfolding,[],[f55,f73])).
% 1.71/0.60  fof(f55,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f8])).
% 1.71/0.60  fof(f8,axiom,(
% 1.71/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.71/0.60  fof(f84,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 1.71/0.60    inference(definition_unfolding,[],[f65,f72])).
% 1.71/0.60  fof(f65,plain,(
% 1.71/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f32])).
% 1.71/0.60  fof(f32,plain,(
% 1.71/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.71/0.60    inference(ennf_transformation,[],[f7])).
% 1.71/0.60  fof(f7,axiom,(
% 1.71/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.71/0.60  fof(f82,plain,(
% 1.71/0.60    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))))) )),
% 1.71/0.60    inference(definition_unfolding,[],[f60,f72,f73,f73])).
% 1.71/0.60  fof(f60,plain,(
% 1.71/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.71/0.60    inference(cnf_transformation,[],[f12])).
% 1.71/0.60  fof(f12,axiom,(
% 1.71/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.71/0.60  fof(f185,plain,(
% 1.71/0.60    k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.71/0.60    inference(forward_demodulation,[],[f182,f81])).
% 1.71/0.60  fof(f182,plain,(
% 1.71/0.60    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0)))),
% 1.71/0.60    inference(superposition,[],[f83,f144])).
% 1.71/0.60  fof(f144,plain,(
% 1.71/0.60    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 1.71/0.60    inference(resolution,[],[f84,f43])).
% 1.71/0.60  fof(f43,plain,(
% 1.71/0.60    r1_tarski(sK0,sK1)),
% 1.71/0.60    inference(cnf_transformation,[],[f38])).
% 1.71/0.60  fof(f83,plain,(
% 1.71/0.60    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))))) )),
% 1.71/0.60    inference(definition_unfolding,[],[f62,f74,f73,f74])).
% 1.71/0.60  fof(f62,plain,(
% 1.71/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f9])).
% 1.71/0.60  fof(f9,axiom,(
% 1.71/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.71/0.60  fof(f379,plain,(
% 1.71/0.60    ( ! [X6,X7] : (r1_tarski(k10_relat_1(sK2,X6),k10_relat_1(sK2,k3_tarski(k1_enumset1(X6,X6,X7))))) )),
% 1.71/0.60    inference(superposition,[],[f78,f199])).
% 1.71/0.60  fof(f199,plain,(
% 1.71/0.60    ( ! [X0,X1] : (k10_relat_1(sK2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))) )),
% 1.71/0.60    inference(resolution,[],[f85,f42])).
% 1.71/0.60  fof(f42,plain,(
% 1.71/0.60    v1_relat_1(sK2)),
% 1.71/0.60    inference(cnf_transformation,[],[f38])).
% 1.71/0.60  fof(f85,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) )),
% 1.71/0.60    inference(definition_unfolding,[],[f69,f74,f74])).
% 1.71/0.60  fof(f69,plain,(
% 1.71/0.60    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f33])).
% 1.71/0.60  fof(f33,plain,(
% 1.71/0.60    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.71/0.60    inference(ennf_transformation,[],[f22])).
% 1.71/0.60  fof(f22,axiom,(
% 1.71/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 1.71/0.60  fof(f78,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.71/0.60    inference(definition_unfolding,[],[f53,f74])).
% 1.71/0.60  fof(f53,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.71/0.60    inference(cnf_transformation,[],[f13])).
% 1.71/0.60  fof(f13,axiom,(
% 1.71/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.71/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.71/0.60  % SZS output end Proof for theBenchmark
% 1.71/0.60  % (2731)------------------------------
% 1.71/0.60  % (2731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.60  % (2731)Termination reason: Refutation
% 1.71/0.60  
% 1.71/0.60  % (2731)Memory used [KB]: 6652
% 1.71/0.60  % (2731)Time elapsed: 0.160 s
% 1.71/0.60  % (2731)------------------------------
% 1.71/0.60  % (2731)------------------------------
% 1.71/0.60  % (2708)Success in time 0.24 s
%------------------------------------------------------------------------------
