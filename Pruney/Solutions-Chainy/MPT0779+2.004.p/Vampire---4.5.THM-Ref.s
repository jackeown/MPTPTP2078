%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  79 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :   66 ( 104 expanded)
%              Number of equality atoms :   48 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f248])).

fof(f248,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0) ),
    inference(superposition,[],[f21,f246])).

fof(f246,plain,(
    ! [X0] : k2_wellord1(sK1,X0) = k2_wellord1(k2_wellord1(sK1,X0),X0) ),
    inference(forward_demodulation,[],[f245,f25])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f245,plain,(
    ! [X0] : k2_wellord1(k2_wellord1(sK1,X0),X0) = k2_wellord1(sK1,k2_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[],[f242,f46])).

fof(f46,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f45,f25])).

fof(f45,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f242,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) ),
    inference(backward_demodulation,[],[f122,f48])).

fof(f48,plain,(
    ! [X2,X3] : k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))) ),
    inference(superposition,[],[f25,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f122,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(resolution,[],[f43,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(f21,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (30707)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.41  % (30707)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f249,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f248])).
% 0.20/0.41  fof(f248,plain,(
% 0.20/0.41    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0)),
% 0.20/0.41    inference(superposition,[],[f21,f246])).
% 0.20/0.41  fof(f246,plain,(
% 0.20/0.41    ( ! [X0] : (k2_wellord1(sK1,X0) = k2_wellord1(k2_wellord1(sK1,X0),X0)) )),
% 0.20/0.41    inference(forward_demodulation,[],[f245,f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,axiom,(
% 0.20/0.41    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.41  fof(f245,plain,(
% 0.20/0.41    ( ! [X0] : (k2_wellord1(k2_wellord1(sK1,X0),X0) = k2_wellord1(sK1,k2_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.41    inference(superposition,[],[f242,f46])).
% 0.20/0.41  fof(f46,plain,(
% 0.20/0.41    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.20/0.41    inference(forward_demodulation,[],[f45,f25])).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 0.20/0.41    inference(resolution,[],[f26,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,axiom,(
% 0.20/0.41    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,axiom,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.41  fof(f242,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))))) )),
% 0.20/0.41    inference(backward_demodulation,[],[f122,f48])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    ( ! [X2,X3] : (k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)))) )),
% 0.20/0.41    inference(superposition,[],[f25,f42])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f29,f41])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f27,f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f28,f39])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f30,f38])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f32,f37])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f33,f36])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f34,f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,axiom,(
% 0.20/0.41    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,axiom,(
% 0.20/0.41    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.41  fof(f122,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.41    inference(resolution,[],[f43,f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    v1_relat_1(sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) & v1_relat_1(sK1)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ? [X0,X1] : (k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0) & v1_relat_1(X1)) => (k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) & v1_relat_1(sK1))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ? [X0,X1] : (k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0) & v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.20/0.41    inference(negated_conjecture,[],[f13])).
% 0.20/0.41  fof(f13,conjecture,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f31,f41])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.41    inference(ennf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (30707)------------------------------
% 0.20/0.42  % (30707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (30707)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (30707)Memory used [KB]: 1791
% 0.20/0.42  % (30707)Time elapsed: 0.011 s
% 0.20/0.42  % (30707)------------------------------
% 0.20/0.42  % (30707)------------------------------
% 0.20/0.42  % (30694)Success in time 0.062 s
%------------------------------------------------------------------------------
