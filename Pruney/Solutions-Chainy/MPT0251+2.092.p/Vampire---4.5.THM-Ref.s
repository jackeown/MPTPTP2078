%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:48 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 186 expanded)
%              Number of leaves         :   11 (  60 expanded)
%              Depth                    :   19
%              Number of atoms          :   92 ( 225 expanded)
%              Number of equality atoms :   51 ( 178 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f812,plain,(
    $false ),
    inference(subsumption_resolution,[],[f811,f34])).

fof(f34,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f811,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f809,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f54,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f809,plain,(
    ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f808])).

fof(f808,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f58,f736])).

fof(f736,plain,(
    ! [X10,X11] :
      ( k2_xboole_0(X11,X10) = X11
      | ~ r1_tarski(X10,X11) ) ),
    inference(forward_demodulation,[],[f724,f37])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f724,plain,(
    ! [X10,X11] :
      ( k2_xboole_0(X11,k1_xboole_0) = k2_xboole_0(X11,X10)
      | ~ r1_tarski(X10,X11) ) ),
    inference(backward_demodulation,[],[f184,f721])).

fof(f721,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f713,f543])).

fof(f543,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    inference(backward_demodulation,[],[f81,f542])).

fof(f542,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f535,f136])).

fof(f136,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f134,f90])).

fof(f90,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f85,f56])).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f40,f37])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f85,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,k1_xboole_0) ),
    inference(superposition,[],[f45,f56])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f134,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f43,f124])).

fof(f124,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f101,f37])).

fof(f101,plain,(
    ! [X4] : k2_xboole_0(k3_xboole_0(X4,k1_xboole_0),X4) = X4 ),
    inference(superposition,[],[f46,f90])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f535,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f43,f477])).

fof(f477,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f461,f37])).

fof(f461,plain,(
    ! [X19,X18] : k2_xboole_0(k3_xboole_0(X18,X19),X18) = X18 ),
    inference(superposition,[],[f149,f46])).

fof(f149,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f145,f45])).

fof(f145,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k2_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(superposition,[],[f45,f78])).

fof(f78,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f44,f40])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f81,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6) ),
    inference(superposition,[],[f44,f56])).

fof(f713,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f43,f644])).

fof(f644,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(superposition,[],[f544,f37])).

fof(f544,plain,(
    ! [X3] : k2_xboole_0(k3_xboole_0(X3,X3),k1_xboole_0) = X3 ),
    inference(backward_demodulation,[],[f100,f542])).

fof(f100,plain,(
    ! [X3] : k2_xboole_0(k3_xboole_0(X3,X3),k4_xboole_0(k1_xboole_0,X3)) = X3 ),
    inference(superposition,[],[f46,f81])).

fof(f184,plain,(
    ! [X10,X11] :
      ( k2_xboole_0(X11,X10) = k2_xboole_0(X11,k5_xboole_0(X10,X10))
      | ~ r1_tarski(X10,X11) ) ),
    inference(superposition,[],[f45,f76])).

fof(f76,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f43,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f58,plain,(
    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f35,f40])).

fof(f35,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:06:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.39  % (3440)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.42  % (3448)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.18/0.42  % (3448)Refutation not found, incomplete strategy% (3448)------------------------------
% 0.18/0.42  % (3448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.42  % (3448)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.42  
% 0.18/0.42  % (3448)Memory used [KB]: 10618
% 0.18/0.42  % (3448)Time elapsed: 0.046 s
% 0.18/0.42  % (3448)------------------------------
% 0.18/0.42  % (3448)------------------------------
% 0.18/0.43  % (3452)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.44  % (3440)Refutation found. Thanks to Tanya!
% 0.18/0.44  % SZS status Theorem for theBenchmark
% 0.18/0.44  % SZS output start Proof for theBenchmark
% 0.18/0.44  fof(f812,plain,(
% 0.18/0.44    $false),
% 0.18/0.44    inference(subsumption_resolution,[],[f811,f34])).
% 0.18/0.44  fof(f34,plain,(
% 0.18/0.44    r2_hidden(sK0,sK1)),
% 0.18/0.44    inference(cnf_transformation,[],[f27])).
% 0.18/0.44  fof(f27,plain,(
% 0.18/0.44    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.18/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).
% 0.18/0.44  fof(f26,plain,(
% 0.18/0.44    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.18/0.44    introduced(choice_axiom,[])).
% 0.18/0.44  fof(f21,plain,(
% 0.18/0.44    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.18/0.44    inference(ennf_transformation,[],[f19])).
% 0.18/0.44  fof(f19,negated_conjecture,(
% 0.18/0.44    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.18/0.44    inference(negated_conjecture,[],[f18])).
% 0.18/0.44  fof(f18,conjecture,(
% 0.18/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.18/0.44  fof(f811,plain,(
% 0.18/0.44    ~r2_hidden(sK0,sK1)),
% 0.18/0.44    inference(resolution,[],[f809,f118])).
% 0.18/0.44  fof(f118,plain,(
% 0.18/0.44    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.18/0.44    inference(duplicate_literal_removal,[],[f117])).
% 0.18/0.44  fof(f117,plain,(
% 0.18/0.44    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.18/0.44    inference(superposition,[],[f54,f38])).
% 0.18/0.44  fof(f38,plain,(
% 0.18/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f12])).
% 0.18/0.44  fof(f12,axiom,(
% 0.18/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.44  fof(f54,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f33])).
% 0.18/0.44  fof(f33,plain,(
% 0.18/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.18/0.44    inference(flattening,[],[f32])).
% 0.18/0.44  fof(f32,plain,(
% 0.18/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.18/0.44    inference(nnf_transformation,[],[f17])).
% 0.18/0.44  fof(f17,axiom,(
% 0.18/0.44    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.18/0.44  fof(f809,plain,(
% 0.18/0.44    ~r1_tarski(k1_tarski(sK0),sK1)),
% 0.18/0.44    inference(trivial_inequality_removal,[],[f808])).
% 0.18/0.44  fof(f808,plain,(
% 0.18/0.44    sK1 != sK1 | ~r1_tarski(k1_tarski(sK0),sK1)),
% 0.18/0.44    inference(superposition,[],[f58,f736])).
% 0.18/0.44  fof(f736,plain,(
% 0.18/0.44    ( ! [X10,X11] : (k2_xboole_0(X11,X10) = X11 | ~r1_tarski(X10,X11)) )),
% 0.18/0.44    inference(forward_demodulation,[],[f724,f37])).
% 0.18/0.44  fof(f37,plain,(
% 0.18/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.44    inference(cnf_transformation,[],[f6])).
% 0.18/0.44  fof(f6,axiom,(
% 0.18/0.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.18/0.44  fof(f724,plain,(
% 0.18/0.44    ( ! [X10,X11] : (k2_xboole_0(X11,k1_xboole_0) = k2_xboole_0(X11,X10) | ~r1_tarski(X10,X11)) )),
% 0.18/0.44    inference(backward_demodulation,[],[f184,f721])).
% 0.18/0.44  fof(f721,plain,(
% 0.18/0.44    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.18/0.44    inference(forward_demodulation,[],[f713,f543])).
% 0.18/0.44  fof(f543,plain,(
% 0.18/0.44    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) )),
% 0.18/0.44    inference(backward_demodulation,[],[f81,f542])).
% 0.18/0.44  fof(f542,plain,(
% 0.18/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.18/0.44    inference(forward_demodulation,[],[f535,f136])).
% 0.18/0.44  fof(f136,plain,(
% 0.18/0.44    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.18/0.44    inference(forward_demodulation,[],[f134,f90])).
% 0.18/0.44  fof(f90,plain,(
% 0.18/0.44    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 0.18/0.44    inference(forward_demodulation,[],[f85,f56])).
% 0.18/0.44  fof(f56,plain,(
% 0.18/0.44    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.18/0.44    inference(superposition,[],[f40,f37])).
% 0.18/0.44  fof(f40,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f1])).
% 0.18/0.44  fof(f1,axiom,(
% 0.18/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.18/0.44  fof(f85,plain,(
% 0.18/0.44    ( ! [X6] : (k2_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,k1_xboole_0)) )),
% 0.18/0.44    inference(superposition,[],[f45,f56])).
% 0.18/0.44  fof(f45,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.18/0.44    inference(cnf_transformation,[],[f8])).
% 0.18/0.44  fof(f8,axiom,(
% 0.18/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.18/0.44  fof(f134,plain,(
% 0.18/0.44    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.18/0.44    inference(superposition,[],[f43,f124])).
% 0.18/0.44  fof(f124,plain,(
% 0.18/0.44    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.18/0.44    inference(superposition,[],[f101,f37])).
% 0.18/0.44  fof(f101,plain,(
% 0.18/0.44    ( ! [X4] : (k2_xboole_0(k3_xboole_0(X4,k1_xboole_0),X4) = X4) )),
% 0.18/0.44    inference(superposition,[],[f46,f90])).
% 0.18/0.44  fof(f46,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.18/0.44    inference(cnf_transformation,[],[f10])).
% 0.18/0.44  fof(f10,axiom,(
% 0.18/0.44    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.18/0.44  fof(f43,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.44    inference(cnf_transformation,[],[f5])).
% 0.18/0.44  fof(f5,axiom,(
% 0.18/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.18/0.44  fof(f535,plain,(
% 0.18/0.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.18/0.44    inference(superposition,[],[f43,f477])).
% 0.18/0.44  fof(f477,plain,(
% 0.18/0.44    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X7)) )),
% 0.18/0.44    inference(superposition,[],[f461,f37])).
% 0.18/0.44  fof(f461,plain,(
% 0.18/0.44    ( ! [X19,X18] : (k2_xboole_0(k3_xboole_0(X18,X19),X18) = X18) )),
% 0.18/0.44    inference(superposition,[],[f149,f46])).
% 0.18/0.44  fof(f149,plain,(
% 0.18/0.44    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 0.18/0.44    inference(forward_demodulation,[],[f145,f45])).
% 0.18/0.44  fof(f145,plain,(
% 0.18/0.44    ( ! [X4,X3] : (k2_xboole_0(X3,k2_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 0.18/0.44    inference(superposition,[],[f45,f78])).
% 0.18/0.44  fof(f78,plain,(
% 0.18/0.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 0.18/0.44    inference(superposition,[],[f44,f40])).
% 0.18/0.44  fof(f44,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f9])).
% 0.18/0.44  fof(f9,axiom,(
% 0.18/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.18/0.44  fof(f81,plain,(
% 0.18/0.44    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6)) )),
% 0.18/0.44    inference(superposition,[],[f44,f56])).
% 0.18/0.44  fof(f713,plain,(
% 0.18/0.44    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.18/0.44    inference(superposition,[],[f43,f644])).
% 0.18/0.44  fof(f644,plain,(
% 0.18/0.44    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 0.18/0.44    inference(superposition,[],[f544,f37])).
% 0.18/0.44  fof(f544,plain,(
% 0.18/0.44    ( ! [X3] : (k2_xboole_0(k3_xboole_0(X3,X3),k1_xboole_0) = X3) )),
% 0.18/0.44    inference(backward_demodulation,[],[f100,f542])).
% 0.18/0.44  fof(f100,plain,(
% 0.18/0.44    ( ! [X3] : (k2_xboole_0(k3_xboole_0(X3,X3),k4_xboole_0(k1_xboole_0,X3)) = X3) )),
% 0.18/0.44    inference(superposition,[],[f46,f81])).
% 0.18/0.44  fof(f184,plain,(
% 0.18/0.44    ( ! [X10,X11] : (k2_xboole_0(X11,X10) = k2_xboole_0(X11,k5_xboole_0(X10,X10)) | ~r1_tarski(X10,X11)) )),
% 0.18/0.44    inference(superposition,[],[f45,f76])).
% 0.18/0.44  fof(f76,plain,(
% 0.18/0.44    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) )),
% 0.18/0.44    inference(superposition,[],[f43,f49])).
% 0.18/0.44  fof(f49,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f24])).
% 0.18/0.44  fof(f24,plain,(
% 0.18/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.18/0.44    inference(ennf_transformation,[],[f7])).
% 0.18/0.44  fof(f7,axiom,(
% 0.18/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.18/0.44  fof(f58,plain,(
% 0.18/0.44    sK1 != k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.18/0.44    inference(superposition,[],[f35,f40])).
% 0.18/0.44  fof(f35,plain,(
% 0.18/0.44    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.18/0.44    inference(cnf_transformation,[],[f27])).
% 0.18/0.44  % SZS output end Proof for theBenchmark
% 0.18/0.44  % (3440)------------------------------
% 0.18/0.44  % (3440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.44  % (3440)Termination reason: Refutation
% 0.18/0.44  
% 0.18/0.44  % (3440)Memory used [KB]: 2046
% 0.18/0.44  % (3440)Time elapsed: 0.067 s
% 0.18/0.44  % (3440)------------------------------
% 0.18/0.44  % (3440)------------------------------
% 0.18/0.44  % (3436)Success in time 0.1 s
%------------------------------------------------------------------------------
