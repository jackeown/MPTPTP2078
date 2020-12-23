%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:57 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 253 expanded)
%              Number of leaves         :   17 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :  120 ( 376 expanded)
%              Number of equality atoms :   84 ( 245 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f53,f243])).

fof(f243,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(forward_demodulation,[],[f242,f55])).

fof(f55,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f242,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1)))) ),
    inference(subsumption_resolution,[],[f227,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(backward_demodulation,[],[f77,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f54,f118])).

fof(f118,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | k4_xboole_0(X3,k1_xboole_0) = X3 ) ),
    inference(superposition,[],[f67,f97])).

fof(f97,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f91,f75])).

fof(f75,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f72,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f56,f54])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f72,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f40,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f56,f54])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f91,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f57,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f72,f56])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != X1
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f65,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f77,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)) ),
    inference(resolution,[],[f62,f42])).

fof(f62,plain,(
    ! [X1] : ~ r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f44,f49,f49])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f227,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1))))
      | k1_xboole_0 = k1_enumset1(X1,X1,X1) ) ),
    inference(superposition,[],[f145,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f46,f48,f49])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f145,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f135,f123])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f58,f55])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f48,f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f53,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f28,f35,f34])).

fof(f28,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:45:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (18319)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (18320)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (18311)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (18306)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (18330)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (18322)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (18309)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (18309)Refutation not found, incomplete strategy% (18309)------------------------------
% 0.22/0.54  % (18309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18309)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18309)Memory used [KB]: 1663
% 0.22/0.54  % (18309)Time elapsed: 0.123 s
% 0.22/0.54  % (18309)------------------------------
% 0.22/0.54  % (18309)------------------------------
% 0.22/0.54  % (18332)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (18332)Refutation not found, incomplete strategy% (18332)------------------------------
% 0.22/0.54  % (18332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18315)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (18332)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18332)Memory used [KB]: 10618
% 0.22/0.54  % (18332)Time elapsed: 0.125 s
% 0.22/0.54  % (18332)------------------------------
% 0.22/0.54  % (18332)------------------------------
% 0.22/0.54  % (18313)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (18312)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (18325)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (18314)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (18325)Refutation not found, incomplete strategy% (18325)------------------------------
% 0.22/0.55  % (18325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18310)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (18319)Refutation not found, incomplete strategy% (18319)------------------------------
% 0.22/0.55  % (18319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18319)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18319)Memory used [KB]: 6140
% 0.22/0.55  % (18319)Time elapsed: 0.135 s
% 0.22/0.55  % (18319)------------------------------
% 0.22/0.55  % (18319)------------------------------
% 0.22/0.55  % (18325)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18325)Memory used [KB]: 1663
% 0.22/0.55  % (18325)Time elapsed: 0.102 s
% 0.22/0.55  % (18325)------------------------------
% 0.22/0.55  % (18325)------------------------------
% 0.22/0.55  % (18320)Refutation not found, incomplete strategy% (18320)------------------------------
% 0.22/0.55  % (18320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18320)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18320)Memory used [KB]: 10618
% 0.22/0.55  % (18320)Time elapsed: 0.135 s
% 0.22/0.55  % (18320)------------------------------
% 0.22/0.55  % (18320)------------------------------
% 0.22/0.55  % (18326)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (18333)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (18335)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (18326)Refutation not found, incomplete strategy% (18326)------------------------------
% 0.22/0.55  % (18326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18326)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18326)Memory used [KB]: 1663
% 0.22/0.55  % (18326)Time elapsed: 0.135 s
% 0.22/0.55  % (18326)------------------------------
% 0.22/0.55  % (18326)------------------------------
% 0.22/0.55  % (18336)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (18327)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (18336)Refutation not found, incomplete strategy% (18336)------------------------------
% 0.22/0.55  % (18336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18336)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18336)Memory used [KB]: 10618
% 0.22/0.55  % (18336)Time elapsed: 0.140 s
% 0.22/0.55  % (18336)------------------------------
% 0.22/0.55  % (18336)------------------------------
% 0.22/0.55  % (18329)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (18334)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (18335)Refutation not found, incomplete strategy% (18335)------------------------------
% 0.22/0.55  % (18335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18335)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18335)Memory used [KB]: 6140
% 0.22/0.55  % (18335)Time elapsed: 0.140 s
% 0.22/0.55  % (18335)------------------------------
% 0.22/0.55  % (18335)------------------------------
% 0.22/0.55  % (18334)Refutation not found, incomplete strategy% (18334)------------------------------
% 0.22/0.55  % (18334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18334)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18334)Memory used [KB]: 6140
% 0.22/0.55  % (18334)Time elapsed: 0.134 s
% 0.22/0.55  % (18334)------------------------------
% 0.22/0.55  % (18334)------------------------------
% 0.22/0.55  % (18317)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (18328)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (18318)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (18322)Refutation not found, incomplete strategy% (18322)------------------------------
% 0.22/0.56  % (18322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18322)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18322)Memory used [KB]: 1663
% 0.22/0.56  % (18322)Time elapsed: 0.105 s
% 0.22/0.56  % (18322)------------------------------
% 0.22/0.56  % (18322)------------------------------
% 0.22/0.56  % (18324)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (18324)Refutation not found, incomplete strategy% (18324)------------------------------
% 0.22/0.56  % (18324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18324)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18324)Memory used [KB]: 10618
% 0.22/0.56  % (18324)Time elapsed: 0.144 s
% 0.22/0.56  % (18324)------------------------------
% 0.22/0.56  % (18324)------------------------------
% 0.22/0.56  % (18321)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (18331)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (18318)Refutation not found, incomplete strategy% (18318)------------------------------
% 0.22/0.56  % (18318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18318)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18318)Memory used [KB]: 10618
% 0.22/0.56  % (18318)Time elapsed: 0.147 s
% 0.22/0.56  % (18318)------------------------------
% 0.22/0.56  % (18318)------------------------------
% 0.22/0.56  % (18323)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (18337)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (18337)Refutation not found, incomplete strategy% (18337)------------------------------
% 0.22/0.57  % (18337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (18337)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (18337)Memory used [KB]: 1663
% 0.22/0.57  % (18337)Time elapsed: 0.001 s
% 0.22/0.57  % (18337)------------------------------
% 0.22/0.57  % (18337)------------------------------
% 1.59/0.57  % (18330)Refutation found. Thanks to Tanya!
% 1.59/0.57  % SZS status Theorem for theBenchmark
% 1.59/0.57  % SZS output start Proof for theBenchmark
% 1.59/0.57  fof(f279,plain,(
% 1.59/0.57    $false),
% 1.59/0.57    inference(trivial_inequality_removal,[],[f272])).
% 1.59/0.57  fof(f272,plain,(
% 1.59/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.59/0.57    inference(superposition,[],[f53,f243])).
% 1.59/0.57  fof(f243,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.59/0.57    inference(forward_demodulation,[],[f242,f55])).
% 1.59/0.57  fof(f55,plain,(
% 1.59/0.57    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.59/0.57    inference(definition_unfolding,[],[f30,f49])).
% 1.59/0.57  fof(f49,plain,(
% 1.59/0.57    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.59/0.57    inference(definition_unfolding,[],[f31,f34])).
% 1.59/0.57  fof(f34,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f11])).
% 1.59/0.57  fof(f11,axiom,(
% 1.59/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.57  fof(f31,plain,(
% 1.59/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f10])).
% 1.59/0.57  fof(f10,axiom,(
% 1.59/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.57  fof(f30,plain,(
% 1.59/0.57    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.59/0.57    inference(cnf_transformation,[],[f16])).
% 1.59/0.57  fof(f16,axiom,(
% 1.59/0.57    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.59/0.57  fof(f242,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1))))) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f227,f123])).
% 1.59/0.57  fof(f123,plain,(
% 1.59/0.57    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 1.59/0.57    inference(backward_demodulation,[],[f77,f122])).
% 1.59/0.57  fof(f122,plain,(
% 1.59/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.59/0.57    inference(backward_demodulation,[],[f54,f118])).
% 1.59/0.57  fof(f118,plain,(
% 1.59/0.57    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 1.59/0.57    inference(trivial_inequality_removal,[],[f117])).
% 1.59/0.57  fof(f117,plain,(
% 1.59/0.57    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 1.59/0.57    inference(superposition,[],[f67,f97])).
% 1.59/0.57  fof(f97,plain,(
% 1.59/0.57    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.59/0.57    inference(forward_demodulation,[],[f91,f75])).
% 1.59/0.57  fof(f75,plain,(
% 1.59/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.59/0.57    inference(resolution,[],[f72,f63])).
% 1.59/0.57  fof(f63,plain,(
% 1.59/0.57    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k1_xboole_0),X0)) )),
% 1.59/0.57    inference(superposition,[],[f56,f54])).
% 1.59/0.57  fof(f56,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.59/0.57    inference(definition_unfolding,[],[f32,f35])).
% 1.59/0.57  fof(f35,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f6])).
% 1.59/0.57  fof(f6,axiom,(
% 1.59/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.59/0.57  fof(f32,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f3])).
% 1.59/0.57  fof(f3,axiom,(
% 1.59/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.59/0.57  fof(f72,plain,(
% 1.59/0.57    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4) )),
% 1.59/0.57    inference(resolution,[],[f40,f64])).
% 1.59/0.57  fof(f64,plain,(
% 1.59/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.57    inference(superposition,[],[f56,f54])).
% 1.59/0.57  fof(f40,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f26])).
% 1.59/0.57  fof(f26,plain,(
% 1.59/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.57    inference(flattening,[],[f25])).
% 1.59/0.57  fof(f25,plain,(
% 1.59/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.57    inference(nnf_transformation,[],[f2])).
% 1.59/0.57  fof(f2,axiom,(
% 1.59/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.57  fof(f91,plain,(
% 1.59/0.57    ( ! [X3] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.59/0.57    inference(superposition,[],[f57,f74])).
% 1.59/0.57  fof(f74,plain,(
% 1.59/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.59/0.57    inference(resolution,[],[f72,f56])).
% 1.59/0.57  fof(f57,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.59/0.57    inference(definition_unfolding,[],[f36,f35])).
% 1.59/0.57  fof(f36,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f5])).
% 1.59/0.57  fof(f5,axiom,(
% 1.59/0.57    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.59/0.57  fof(f67,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != X1 | k4_xboole_0(X0,X1) = X0) )),
% 1.59/0.57    inference(resolution,[],[f65,f42])).
% 1.59/0.57  fof(f42,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.59/0.57    inference(cnf_transformation,[],[f27])).
% 1.59/0.57  fof(f27,plain,(
% 1.59/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.59/0.57    inference(nnf_transformation,[],[f7])).
% 1.59/0.57  fof(f7,axiom,(
% 1.59/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.59/0.57  fof(f65,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k4_xboole_0(X0,X1) = X0) )),
% 1.59/0.57    inference(resolution,[],[f41,f37])).
% 1.59/0.57  fof(f37,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f20])).
% 1.59/0.57  fof(f20,plain,(
% 1.59/0.57    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f1])).
% 1.59/0.57  fof(f1,axiom,(
% 1.59/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.59/0.57  fof(f41,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.59/0.57    inference(cnf_transformation,[],[f27])).
% 1.59/0.57  fof(f54,plain,(
% 1.59/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.59/0.57    inference(definition_unfolding,[],[f29,f35])).
% 1.59/0.57  fof(f29,plain,(
% 1.59/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f4])).
% 1.59/0.57  fof(f4,axiom,(
% 1.59/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.59/0.57  fof(f77,plain,(
% 1.59/0.57    ( ! [X0] : (k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) )),
% 1.59/0.57    inference(resolution,[],[f62,f42])).
% 1.59/0.57  fof(f62,plain,(
% 1.59/0.57    ( ! [X1] : (~r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 1.59/0.57    inference(equality_resolution,[],[f59])).
% 1.59/0.57  fof(f59,plain,(
% 1.59/0.57    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 1.59/0.57    inference(definition_unfolding,[],[f44,f49,f49])).
% 1.59/0.57  fof(f44,plain,(
% 1.59/0.57    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f22])).
% 1.59/0.57  fof(f22,plain,(
% 1.59/0.57    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.59/0.57    inference(ennf_transformation,[],[f14])).
% 1.59/0.57  fof(f14,axiom,(
% 1.59/0.57    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 1.59/0.57  fof(f227,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1)))) | k1_xboole_0 = k1_enumset1(X1,X1,X1)) )),
% 1.59/0.57    inference(superposition,[],[f145,f52])).
% 1.59/0.57  fof(f52,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 1.59/0.57    inference(definition_unfolding,[],[f45,f50])).
% 1.59/0.57  fof(f50,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 1.59/0.57    inference(definition_unfolding,[],[f46,f48,f49])).
% 1.59/0.57  fof(f48,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.59/0.57    inference(definition_unfolding,[],[f33,f34])).
% 1.59/0.57  fof(f33,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f13])).
% 1.59/0.57  fof(f13,axiom,(
% 1.59/0.57    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.59/0.57  fof(f46,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f8])).
% 1.59/0.57  fof(f8,axiom,(
% 1.59/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.59/0.57  fof(f45,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f12])).
% 1.59/0.57  fof(f12,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.57  fof(f145,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) | k1_xboole_0 = X1) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f135,f123])).
% 1.59/0.57  fof(f135,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.59/0.57    inference(superposition,[],[f58,f55])).
% 1.59/0.57  fof(f58,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.59/0.57    inference(definition_unfolding,[],[f43,f48,f35])).
% 1.59/0.57  fof(f43,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.59/0.57    inference(cnf_transformation,[],[f21])).
% 1.59/0.57  fof(f21,plain,(
% 1.59/0.57    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.59/0.57    inference(ennf_transformation,[],[f15])).
% 1.59/0.57  fof(f15,axiom,(
% 1.59/0.57    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.59/0.57  fof(f53,plain,(
% 1.59/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 1.59/0.57    inference(definition_unfolding,[],[f28,f35,f34])).
% 1.59/0.57  fof(f28,plain,(
% 1.59/0.57    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.59/0.57    inference(cnf_transformation,[],[f24])).
% 1.59/0.57  fof(f24,plain,(
% 1.59/0.57    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.59/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f23])).
% 1.59/0.57  fof(f23,plain,(
% 1.59/0.57    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f19,plain,(
% 1.59/0.57    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f18])).
% 1.59/0.57  fof(f18,negated_conjecture,(
% 1.59/0.57    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.59/0.57    inference(negated_conjecture,[],[f17])).
% 1.59/0.57  fof(f17,conjecture,(
% 1.59/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.59/0.57  % SZS output end Proof for theBenchmark
% 1.59/0.57  % (18330)------------------------------
% 1.59/0.57  % (18330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (18330)Termination reason: Refutation
% 1.59/0.57  
% 1.59/0.57  % (18330)Memory used [KB]: 6396
% 1.59/0.57  % (18330)Time elapsed: 0.118 s
% 1.59/0.57  % (18330)------------------------------
% 1.59/0.57  % (18330)------------------------------
% 1.59/0.57  % (18299)Success in time 0.198 s
%------------------------------------------------------------------------------
