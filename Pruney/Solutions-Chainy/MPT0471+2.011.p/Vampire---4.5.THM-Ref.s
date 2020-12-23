%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  60 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :   14
%              Number of atoms          :   54 (  69 expanded)
%              Number of equality atoms :   40 (  55 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(subsumption_resolution,[],[f45,f18])).

fof(f18,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f14])).

fof(f14,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f45,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f44,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f44,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f43,f21])).

fof(f21,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f43,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f42,f23])).

fof(f42,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f41,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f41,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_relat_1(k1_xboole_0),k1_setfam_1(k3_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f40,f20])).

fof(f20,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k5_xboole_0(k2_relat_1(k1_xboole_0),k1_setfam_1(k3_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))))) ),
    inference(resolution,[],[f38,f39])).

fof(f39,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k5_xboole_0(k2_relat_1(X0),k1_setfam_1(k3_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k1_relat_1(X0))))) ) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)))) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:55:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.40  % (14320)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.40  % (14320)Refutation found. Thanks to Tanya!
% 0.21/0.40  % SZS status Theorem for theBenchmark
% 0.21/0.40  % SZS output start Proof for theBenchmark
% 0.21/0.40  fof(f46,plain,(
% 0.21/0.40    $false),
% 0.21/0.40    inference(subsumption_resolution,[],[f45,f18])).
% 0.21/0.40  fof(f18,plain,(
% 0.21/0.40    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.40    inference(cnf_transformation,[],[f15])).
% 0.21/0.40  fof(f15,plain,(
% 0.21/0.40    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.40    inference(flattening,[],[f14])).
% 0.21/0.40  fof(f14,negated_conjecture,(
% 0.21/0.40    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.40    inference(negated_conjecture,[],[f13])).
% 0.21/0.40  fof(f13,conjecture,(
% 0.21/0.40    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.21/0.40  fof(f45,plain,(
% 0.21/0.40    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.40    inference(forward_demodulation,[],[f44,f23])).
% 0.21/0.40  fof(f23,plain,(
% 0.21/0.40    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.40    inference(cnf_transformation,[],[f4])).
% 0.21/0.40  fof(f4,axiom,(
% 0.21/0.40    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.40  fof(f44,plain,(
% 0.21/0.40    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.40    inference(forward_demodulation,[],[f43,f21])).
% 0.21/0.40  fof(f21,plain,(
% 0.21/0.40    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.40    inference(cnf_transformation,[],[f12])).
% 0.21/0.40  fof(f12,axiom,(
% 0.21/0.40    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.40  fof(f43,plain,(
% 0.21/0.40    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.21/0.40    inference(forward_demodulation,[],[f42,f23])).
% 0.21/0.40  fof(f42,plain,(
% 0.21/0.40    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0))),
% 0.21/0.40    inference(forward_demodulation,[],[f41,f37])).
% 0.21/0.40  fof(f37,plain,(
% 0.21/0.40    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k1_xboole_0))) )),
% 0.21/0.40    inference(definition_unfolding,[],[f22,f34])).
% 0.21/0.40  fof(f34,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.40    inference(definition_unfolding,[],[f26,f33])).
% 0.21/0.40  fof(f33,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.40    inference(definition_unfolding,[],[f27,f32])).
% 0.21/0.40  fof(f32,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.40    inference(definition_unfolding,[],[f30,f31])).
% 0.21/0.40  fof(f31,plain,(
% 0.21/0.40    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f8])).
% 0.21/0.40  fof(f8,axiom,(
% 0.21/0.40    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.40  fof(f30,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f7])).
% 0.21/0.40  fof(f7,axiom,(
% 0.21/0.40    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.40  fof(f27,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f6])).
% 0.21/0.40  fof(f6,axiom,(
% 0.21/0.40    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.40  fof(f26,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.40    inference(cnf_transformation,[],[f9])).
% 0.21/0.40  fof(f9,axiom,(
% 0.21/0.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.40  fof(f22,plain,(
% 0.21/0.40    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f3])).
% 0.21/0.40  fof(f3,axiom,(
% 0.21/0.40    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.40  fof(f41,plain,(
% 0.21/0.40    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_relat_1(k1_xboole_0),k1_setfam_1(k3_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0))))),
% 0.21/0.40    inference(forward_demodulation,[],[f40,f20])).
% 0.21/0.40  fof(f20,plain,(
% 0.21/0.40    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.40    inference(cnf_transformation,[],[f12])).
% 0.21/0.40  fof(f40,plain,(
% 0.21/0.40    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k5_xboole_0(k2_relat_1(k1_xboole_0),k1_setfam_1(k3_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))))),
% 0.21/0.40    inference(resolution,[],[f38,f39])).
% 0.21/0.40  fof(f39,plain,(
% 0.21/0.40    v1_relat_1(k1_xboole_0)),
% 0.21/0.40    inference(resolution,[],[f24,f19])).
% 0.21/0.40  fof(f19,plain,(
% 0.21/0.40    v1_xboole_0(k1_xboole_0)),
% 0.21/0.40    inference(cnf_transformation,[],[f1])).
% 0.21/0.40  fof(f1,axiom,(
% 0.21/0.40    v1_xboole_0(k1_xboole_0)),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.40  fof(f24,plain,(
% 0.21/0.40    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f16])).
% 0.21/0.40  fof(f16,plain,(
% 0.21/0.40    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.40    inference(ennf_transformation,[],[f10])).
% 0.21/0.40  fof(f10,axiom,(
% 0.21/0.40    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.40  fof(f38,plain,(
% 0.21/0.40    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k5_xboole_0(k2_relat_1(X0),k1_setfam_1(k3_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k1_relat_1(X0)))))) )),
% 0.21/0.40    inference(definition_unfolding,[],[f25,f36])).
% 0.21/0.40  fof(f36,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0))))) )),
% 0.21/0.40    inference(definition_unfolding,[],[f28,f35])).
% 0.21/0.40  fof(f35,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.21/0.40    inference(definition_unfolding,[],[f29,f34])).
% 0.21/0.40  fof(f29,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.40    inference(cnf_transformation,[],[f2])).
% 0.21/0.40  fof(f2,axiom,(
% 0.21/0.40    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.40  fof(f28,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.40    inference(cnf_transformation,[],[f5])).
% 0.21/0.40  fof(f5,axiom,(
% 0.21/0.40    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.40  fof(f25,plain,(
% 0.21/0.40    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f17])).
% 0.21/0.40  fof(f17,plain,(
% 0.21/0.40    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.40    inference(ennf_transformation,[],[f11])).
% 0.21/0.40  fof(f11,axiom,(
% 0.21/0.40    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.40  % SZS output end Proof for theBenchmark
% 0.21/0.40  % (14320)------------------------------
% 0.21/0.40  % (14320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.40  % (14320)Termination reason: Refutation
% 0.21/0.40  
% 0.21/0.40  % (14320)Memory used [KB]: 1535
% 0.21/0.40  % (14320)Time elapsed: 0.003 s
% 0.21/0.40  % (14320)------------------------------
% 0.21/0.40  % (14320)------------------------------
% 0.21/0.41  % (14307)Success in time 0.057 s
%------------------------------------------------------------------------------
