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
% DateTime   : Thu Dec  3 12:44:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 199 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 274 expanded)
%              Number of equality atoms :   72 ( 191 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f395,plain,(
    $false ),
    inference(subsumption_resolution,[],[f394,f60])).

fof(f60,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f32,f33])).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f394,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f393,f281])).

fof(f281,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f279,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f55,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f34,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f279,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f58,f56])).

fof(f56,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f54])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f393,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f389,f261])).

fof(f261,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f70,f219])).

fof(f219,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f125,f218])).

fof(f218,plain,(
    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f215,f98])).

fof(f98,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f215,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f125,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f100,f98])).

fof(f100,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f45,f85])).

fof(f85,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f44,f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f70,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f389,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f382,f287])).

fof(f287,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f277,f58])).

fof(f277,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(superposition,[],[f58,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f53,f53])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f382,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f347,f31])).

fof(f347,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X1,k4_xboole_0(X0,X1)) = k4_subset_1(X0,X1,X0) ) ),
    inference(resolution,[],[f63,f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f36,f33])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f59,f58])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f54])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (32191)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.43  % (32191)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f395,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(subsumption_resolution,[],[f394,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 0.20/0.43    inference(backward_demodulation,[],[f32,f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,axiom,(
% 0.20/0.43    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.20/0.43    inference(negated_conjecture,[],[f19])).
% 0.20/0.43  fof(f19,conjecture,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 0.20/0.43  fof(f394,plain,(
% 0.20/0.43    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f393,f281])).
% 0.20/0.43  fof(f281,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(forward_demodulation,[],[f279,f61])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.43    inference(backward_demodulation,[],[f55,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f34,f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.43  fof(f279,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.20/0.43    inference(superposition,[],[f58,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f37,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f40,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f41,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f49,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.43    inference(rectify,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f42,f54])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.43  fof(f393,plain,(
% 0.20/0.43    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.43    inference(forward_demodulation,[],[f389,f261])).
% 0.20/0.43  fof(f261,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.20/0.43    inference(superposition,[],[f70,f219])).
% 0.20/0.43  fof(f219,plain,(
% 0.20/0.43    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.43    inference(backward_demodulation,[],[f125,f218])).
% 0.20/0.43  fof(f218,plain,(
% 0.20/0.43    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.43    inference(forward_demodulation,[],[f215,f98])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.43    inference(resolution,[],[f45,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f29])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.43  fof(f215,plain,(
% 0.20/0.43    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.20/0.43    inference(resolution,[],[f46,f31])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.43    inference(forward_demodulation,[],[f100,f98])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))),
% 0.20/0.43    inference(resolution,[],[f45,f85])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.43    inference(resolution,[],[f44,f31])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.43    inference(resolution,[],[f48,f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.43    inference(nnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.43  fof(f389,plain,(
% 0.20/0.43    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.20/0.43    inference(superposition,[],[f382,f287])).
% 0.20/0.43  fof(f287,plain,(
% 0.20/0.43    ( ! [X4,X3] : (k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 0.20/0.43    inference(superposition,[],[f277,f58])).
% 0.20/0.43  fof(f277,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.20/0.43    inference(superposition,[],[f58,f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f39,f53,f53])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.43  fof(f382,plain,(
% 0.20/0.43    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.43    inference(resolution,[],[f347,f31])).
% 0.20/0.43  fof(f347,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X1,k4_xboole_0(X0,X1)) = k4_subset_1(X0,X1,X0)) )),
% 0.20/0.43    inference(resolution,[],[f63,f62])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f36,f33])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,axiom,(
% 0.20/0.43    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f59,f58])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f50,f54])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(flattening,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.43    inference(ennf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (32191)------------------------------
% 0.20/0.43  % (32191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (32191)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (32191)Memory used [KB]: 1791
% 0.20/0.43  % (32191)Time elapsed: 0.014 s
% 0.20/0.43  % (32191)------------------------------
% 0.20/0.43  % (32191)------------------------------
% 0.20/0.44  % (32177)Success in time 0.076 s
%------------------------------------------------------------------------------
