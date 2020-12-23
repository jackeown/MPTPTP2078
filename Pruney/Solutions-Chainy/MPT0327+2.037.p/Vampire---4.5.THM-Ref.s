%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 270 expanded)
%              Number of leaves         :   17 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 334 expanded)
%              Number of equality atoms :   69 ( 232 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f686,plain,(
    $false ),
    inference(subsumption_resolution,[],[f685,f285])).

fof(f285,plain,(
    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f278,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f278,plain,(
    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f259,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f259,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f258,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f58,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f258,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f60,f257])).

fof(f257,plain,(
    ! [X19] : k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,X19))) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),X19) ),
    inference(forward_demodulation,[],[f223,f103])).

fof(f103,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f93,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(unit_resulting_resolution,[],[f45,f41])).

fof(f45,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f93,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) = X0 ),
    inference(unit_resulting_resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f223,plain,(
    ! [X19] : k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,X19))) = k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0),X19) ),
    inference(superposition,[],[f51,f88])).

fof(f88,plain,(
    k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f85,f41])).

fof(f85,plain,(
    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f24,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f24,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f31,f31])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f60,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))) ),
    inference(backward_demodulation,[],[f50,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f31,f31])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f25,f47,f48,f48])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f25,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f685,plain,(
    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f684,f319])).

fof(f319,plain,(
    sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f179,f316])).

fof(f316,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f315,f103])).

fof(f315,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f293,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f31])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f293,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(superposition,[],[f55,f44])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f47,f46])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

% (17317)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f179,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0)) ),
    inference(superposition,[],[f62,f88])).

fof(f62,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f61,f55])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f54,f55])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f34,f47,f47])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f684,plain,(
    k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f671,f654])).

fof(f654,plain,(
    k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f628,f103])).

fof(f628,plain,(
    k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f151,f88])).

fof(f151,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f49,f53])).

fof(f671,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) ),
    inference(superposition,[],[f55,f165])).

fof(f165,plain,(
    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f142,f103])).

fof(f142,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f53,f88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:42:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (17292)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (17306)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (17298)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (17318)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (17310)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (17300)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (17294)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (17303)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (17291)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (17295)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (17293)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (17311)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (17318)Refutation not found, incomplete strategy% (17318)------------------------------
% 0.21/0.54  % (17318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17315)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (17318)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17318)Memory used [KB]: 6140
% 0.21/0.55  % (17318)Time elapsed: 0.131 s
% 0.21/0.55  % (17318)------------------------------
% 0.21/0.55  % (17318)------------------------------
% 0.21/0.55  % (17316)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (17296)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (17301)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (17297)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (17301)Refutation not found, incomplete strategy% (17301)------------------------------
% 0.21/0.55  % (17301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17307)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (17308)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (17301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17301)Memory used [KB]: 10746
% 0.21/0.55  % (17301)Time elapsed: 0.147 s
% 0.21/0.55  % (17301)------------------------------
% 0.21/0.55  % (17301)------------------------------
% 0.21/0.55  % (17307)Refutation not found, incomplete strategy% (17307)------------------------------
% 0.21/0.55  % (17307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17307)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17307)Memory used [KB]: 10618
% 0.21/0.55  % (17307)Time elapsed: 0.147 s
% 0.21/0.55  % (17307)------------------------------
% 0.21/0.55  % (17307)------------------------------
% 0.21/0.56  % (17305)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (17314)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (17310)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (17299)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (17302)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (17320)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (17320)Refutation not found, incomplete strategy% (17320)------------------------------
% 0.21/0.56  % (17320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17320)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17320)Memory used [KB]: 1663
% 0.21/0.56  % (17320)Time elapsed: 0.145 s
% 0.21/0.56  % (17320)------------------------------
% 0.21/0.56  % (17320)------------------------------
% 0.21/0.56  % (17313)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (17304)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.57  % (17309)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (17319)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (17312)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.57  % (17319)Refutation not found, incomplete strategy% (17319)------------------------------
% 0.21/0.57  % (17319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (17319)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (17319)Memory used [KB]: 10746
% 0.21/0.57  % (17319)Time elapsed: 0.170 s
% 0.21/0.57  % (17319)------------------------------
% 0.21/0.57  % (17319)------------------------------
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f686,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(subsumption_resolution,[],[f685,f285])).
% 0.21/0.58  fof(f285,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.58    inference(forward_demodulation,[],[f278,f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.58  fof(f278,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0))),
% 0.21/0.58    inference(superposition,[],[f259,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.58  fof(f259,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_xboole_0)),
% 0.21/0.58    inference(forward_demodulation,[],[f258,f63])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f58,f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.58  fof(f258,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)))),
% 0.21/0.58    inference(backward_demodulation,[],[f60,f257])).
% 0.21/0.58  fof(f257,plain,(
% 0.21/0.58    ( ! [X19] : (k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,X19))) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),X19)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f223,f103])).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(forward_demodulation,[],[f93,f65])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f45,f41])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,axiom,(
% 0.21/0.58    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) = X0) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f45,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f30,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.58  fof(f223,plain,(
% 0.21/0.58    ( ! [X19] : (k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,X19))) = k4_xboole_0(k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0),X19)) )),
% 0.21/0.58    inference(superposition,[],[f51,f88])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f85,f41])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f24,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f38,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f40,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    r2_hidden(sK0,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.58    inference(negated_conjecture,[],[f20])).
% 0.21/0.58  fof(f20,conjecture,(
% 0.21/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f26,f31,f31])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))))),
% 0.21/0.58    inference(backward_demodulation,[],[f50,f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f32,f31,f31])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))))),
% 0.21/0.58    inference(definition_unfolding,[],[f25,f47,f48,f48])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f33,f31])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f685,plain,(
% 0.21/0.58    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.58    inference(forward_demodulation,[],[f684,f319])).
% 0.21/0.58  fof(f319,plain,(
% 0.21/0.58    sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0)))),
% 0.21/0.58    inference(backward_demodulation,[],[f179,f316])).
% 0.21/0.58  fof(f316,plain,(
% 0.21/0.58    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 0.21/0.58    inference(forward_demodulation,[],[f315,f103])).
% 0.21/0.58  fof(f315,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f293,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f36,f31])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.58  fof(f293,plain,(
% 0.21/0.58    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 0.21/0.58    inference(superposition,[],[f55,f44])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f35,f47,f46])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  % (17317)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.58  fof(f18,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.58  fof(f179,plain,(
% 0.21/0.58    k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0))),
% 0.21/0.58    inference(superposition,[],[f62,f88])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f61,f55])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.58    inference(backward_demodulation,[],[f54,f55])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f34,f47,f47])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.58  fof(f684,plain,(
% 0.21/0.58    k5_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0)))),
% 0.21/0.58    inference(forward_demodulation,[],[f671,f654])).
% 0.21/0.58  fof(f654,plain,(
% 0.21/0.58    k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.58    inference(forward_demodulation,[],[f628,f103])).
% 0.21/0.58  fof(f628,plain,(
% 0.21/0.58    k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0))),
% 0.21/0.58    inference(superposition,[],[f151,f88])).
% 0.21/0.58  fof(f151,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.21/0.58    inference(superposition,[],[f49,f53])).
% 0.21/0.58  fof(f671,plain,(
% 0.21/0.58    k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.58    inference(superposition,[],[f55,f165])).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),
% 0.21/0.58    inference(forward_demodulation,[],[f142,f103])).
% 0.21/0.58  fof(f142,plain,(
% 0.21/0.58    k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0)),
% 0.21/0.58    inference(superposition,[],[f53,f88])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (17310)------------------------------
% 0.21/0.58  % (17310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (17310)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (17310)Memory used [KB]: 2174
% 0.21/0.58  % (17310)Time elapsed: 0.147 s
% 0.21/0.58  % (17310)------------------------------
% 0.21/0.58  % (17310)------------------------------
% 0.21/0.58  % (17290)Success in time 0.215 s
%------------------------------------------------------------------------------
