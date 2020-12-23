%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 147 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  110 ( 275 expanded)
%              Number of equality atoms :   47 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f619,plain,(
    $false ),
    inference(subsumption_resolution,[],[f276,f608])).

fof(f608,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f472,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f472,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,X1)) ),
    inference(forward_demodulation,[],[f465,f351])).

fof(f351,plain,(
    ! [X12] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X12) ),
    inference(forward_demodulation,[],[f340,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f27,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f340,plain,(
    ! [X12,X11] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X11,X12)) = k4_xboole_0(k1_xboole_0,X12) ),
    inference(superposition,[],[f35,f38])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f465,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,X1)) ),
    inference(superposition,[],[f35,f434])).

fof(f434,plain,(
    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f433])).

fof(f433,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f158,f422])).

fof(f422,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f411,f27])).

fof(f411,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f391,f76])).

fof(f76,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f74,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f74,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f28,f65])).

fof(f65,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f34,f23])).

fof(f23,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f391,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(X0,sK2))) ),
    inference(superposition,[],[f363,f27])).

fof(f363,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK2,X0))) ),
    inference(superposition,[],[f355,f28])).

fof(f355,plain,(
    ! [X14] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,X14))) ),
    inference(forward_demodulation,[],[f354,f35])).

fof(f354,plain,(
    ! [X14] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK1,sK2),X14)) ),
    inference(forward_demodulation,[],[f342,f351])).

fof(f342,plain,(
    ! [X14] : k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK1,sK2),X14)) = k4_xboole_0(k1_xboole_0,X14) ),
    inference(superposition,[],[f35,f61])).

fof(f61,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f158,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k3_xboole_0(X3,X2)
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f137,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X1,X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f104,f31])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f29,f47])).

fof(f47,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X3,X2))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f30,f27])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f276,plain,(
    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f263,f32])).

fof(f263,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f106,f22])).

fof(f22,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f106,plain,(
    ! [X4,X5] :
      ( r1_xboole_0(X4,X5)
      | ~ r1_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f29,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f47,f98])).

fof(f98,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f97,f26])).

fof(f97,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f28,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f72,f25])).

fof(f72,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f28,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:11:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (3134)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.44  % (3145)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (3145)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f619,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f276,f608])).
% 0.20/0.46  fof(f608,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,X0))) )),
% 0.20/0.46    inference(superposition,[],[f472,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.46  fof(f472,plain,(
% 0.20/0.46    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,X1))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f465,f351])).
% 0.20/0.46  fof(f351,plain,(
% 0.20/0.46    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X12)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f340,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(superposition,[],[f27,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.46  fof(f340,plain,(
% 0.20/0.46    ( ! [X12,X11] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X11,X12)) = k4_xboole_0(k1_xboole_0,X12)) )),
% 0.20/0.46    inference(superposition,[],[f35,f38])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.46  fof(f465,plain,(
% 0.20/0.46    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,X1))) )),
% 0.20/0.46    inference(superposition,[],[f35,f434])).
% 0.20/0.46  fof(f434,plain,(
% 0.20/0.46    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f433])).
% 0.20/0.46  fof(f433,plain,(
% 0.20/0.46    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)),
% 0.20/0.46    inference(superposition,[],[f158,f422])).
% 0.20/0.46  fof(f422,plain,(
% 0.20/0.46    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.46    inference(forward_demodulation,[],[f411,f27])).
% 0.20/0.46  fof(f411,plain,(
% 0.20/0.46    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK0))),
% 0.20/0.46    inference(superposition,[],[f391,f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    sK0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.46    inference(forward_demodulation,[],[f74,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.46    inference(superposition,[],[f28,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.46    inference(resolution,[],[f34,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    r1_tarski(sK0,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(negated_conjecture,[],[f11])).
% 0.20/0.46  fof(f11,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.46  fof(f391,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(X0,sK2)))) )),
% 0.20/0.46    inference(superposition,[],[f363,f27])).
% 0.20/0.46  fof(f363,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK2,X0)))) )),
% 0.20/0.46    inference(superposition,[],[f355,f28])).
% 0.20/0.46  fof(f355,plain,(
% 0.20/0.46    ( ! [X14] : (k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,X14)))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f354,f35])).
% 0.20/0.46  fof(f354,plain,(
% 0.20/0.46    ( ! [X14] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK1,sK2),X14))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f342,f351])).
% 0.20/0.46  fof(f342,plain,(
% 0.20/0.46    ( ! [X14] : (k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK1,sK2),X14)) = k4_xboole_0(k1_xboole_0,X14)) )),
% 0.20/0.46    inference(superposition,[],[f35,f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.46    inference(resolution,[],[f31,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.46  fof(f158,plain,(
% 0.20/0.46    ( ! [X2,X3] : (k1_xboole_0 != k3_xboole_0(X3,X2) | k1_xboole_0 = k3_xboole_0(X2,X3)) )),
% 0.20/0.46    inference(resolution,[],[f137,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X1,X0) = k1_xboole_0) )),
% 0.20/0.46    inference(resolution,[],[f104,f31])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(resolution,[],[f29,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X3,X2)) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.46    inference(superposition,[],[f30,f27])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f276,plain,(
% 0.20/0.46    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.20/0.46    inference(resolution,[],[f263,f32])).
% 0.20/0.46  fof(f263,plain,(
% 0.20/0.46    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.20/0.46    inference(resolution,[],[f106,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    ( ! [X4,X5] : (r1_xboole_0(X4,X5) | ~r1_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 0.20/0.46    inference(resolution,[],[f29,f99])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 0.20/0.46    inference(superposition,[],[f47,f98])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.46    inference(forward_demodulation,[],[f97,f26])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 0.20/0.46    inference(superposition,[],[f28,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f72,f25])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.20/0.46    inference(superposition,[],[f28,f26])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (3145)------------------------------
% 0.20/0.46  % (3145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (3145)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (3145)Memory used [KB]: 6396
% 0.20/0.46  % (3145)Time elapsed: 0.037 s
% 0.20/0.46  % (3145)------------------------------
% 0.20/0.46  % (3145)------------------------------
% 0.20/0.47  % (3128)Success in time 0.111 s
%------------------------------------------------------------------------------
