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
% DateTime   : Thu Dec  3 12:41:40 EST 2020

% Result     : Theorem 3.53s
% Output     : Refutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 140 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 190 expanded)
%              Number of equality atoms :   37 (  94 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7072,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3485,f3711,f7055,f7071])).

fof(f7071,plain,
    ( ~ spl2_8
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f7062])).

fof(f7062,plain,
    ( $false
    | ~ spl2_8
    | spl2_12 ),
    inference(resolution,[],[f3928,f2442])).

fof(f2442,plain,
    ( r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f2441])).

fof(f2441,plain,
    ( spl2_8
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f3928,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_12 ),
    inference(resolution,[],[f3484,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f3484,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f3482])).

fof(f3482,plain,
    ( spl2_12
  <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f7055,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f7046])).

fof(f7046,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f7038,f739])).

fof(f739,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X2,X1)) ),
    inference(superposition,[],[f388,f44])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f388,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f107,f66])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f107,plain,(
    ! [X6,X5] : r1_tarski(X5,k3_tarski(k2_enumset1(X5,X5,X5,X6))) ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X5,k3_tarski(k2_enumset1(X5,X5,X5,X6))) ) ),
    inference(superposition,[],[f55,f71])).

fof(f71,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f65])).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f7038,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))
    | spl2_8 ),
    inference(resolution,[],[f2443,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f2443,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f2441])).

fof(f3711,plain,(
    spl2_11 ),
    inference(avatar_contradiction_clause,[],[f3702])).

fof(f3702,plain,
    ( $false
    | spl2_11 ),
    inference(resolution,[],[f3694,f388])).

fof(f3694,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | spl2_11 ),
    inference(resolution,[],[f3480,f54])).

fof(f3480,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f3478])).

fof(f3478,plain,
    ( spl2_11
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f3485,plain,
    ( ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f3461,f3482,f3478])).

fof(f3461,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f3256,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f3256,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f68,f3239])).

fof(f3239,plain,(
    ! [X2,X3] : k3_tarski(k2_enumset1(X2,X2,X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f293,f225])).

fof(f225,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f67,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f45,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f293,plain,(
    ! [X2,X3] : k3_tarski(k2_enumset1(X2,X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f74,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f65,f50])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f68,plain,(
    ~ r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f39,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f36])).

fof(f36,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (3784)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  % (3785)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (3789)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (3786)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (3782)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (3790)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (3799)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (3783)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (3793)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (3796)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (3793)Refutation not found, incomplete strategy% (3793)------------------------------
% 0.21/0.48  % (3793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3793)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3793)Memory used [KB]: 10618
% 0.21/0.48  % (3793)Time elapsed: 0.081 s
% 0.21/0.48  % (3793)------------------------------
% 0.21/0.48  % (3793)------------------------------
% 0.21/0.49  % (3787)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (3795)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (3791)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (3798)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (3797)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (3792)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (3788)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (3794)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 3.53/0.81  % (3786)Refutation found. Thanks to Tanya!
% 3.53/0.81  % SZS status Theorem for theBenchmark
% 3.53/0.81  % SZS output start Proof for theBenchmark
% 3.53/0.81  fof(f7072,plain,(
% 3.53/0.81    $false),
% 3.53/0.81    inference(avatar_sat_refutation,[],[f3485,f3711,f7055,f7071])).
% 3.53/0.81  fof(f7071,plain,(
% 3.53/0.81    ~spl2_8 | spl2_12),
% 3.53/0.81    inference(avatar_contradiction_clause,[],[f7062])).
% 3.53/0.81  fof(f7062,plain,(
% 3.53/0.81    $false | (~spl2_8 | spl2_12)),
% 3.53/0.81    inference(resolution,[],[f3928,f2442])).
% 3.53/0.81  fof(f2442,plain,(
% 3.53/0.81    r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~spl2_8),
% 3.53/0.81    inference(avatar_component_clause,[],[f2441])).
% 3.53/0.81  fof(f2441,plain,(
% 3.53/0.81    spl2_8 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.53/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 3.53/0.81  fof(f3928,plain,(
% 3.53/0.81    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_12),
% 3.53/0.81    inference(resolution,[],[f3484,f61])).
% 3.53/0.81  fof(f61,plain,(
% 3.53/0.81    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.53/0.81    inference(cnf_transformation,[],[f31])).
% 3.53/0.81  fof(f31,plain,(
% 3.53/0.81    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.53/0.81    inference(ennf_transformation,[],[f8])).
% 3.53/0.81  fof(f8,axiom,(
% 3.53/0.81    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 3.53/0.81  fof(f3484,plain,(
% 3.53/0.81    ~r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_12),
% 3.53/0.81    inference(avatar_component_clause,[],[f3482])).
% 3.53/0.81  fof(f3482,plain,(
% 3.53/0.81    spl2_12 <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.53/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 3.53/0.81  fof(f7055,plain,(
% 3.53/0.81    spl2_8),
% 3.53/0.81    inference(avatar_contradiction_clause,[],[f7046])).
% 3.53/0.81  fof(f7046,plain,(
% 3.53/0.81    $false | spl2_8),
% 3.53/0.81    inference(resolution,[],[f7038,f739])).
% 3.53/0.81  fof(f739,plain,(
% 3.53/0.81    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X2,X1))) )),
% 3.53/0.81    inference(superposition,[],[f388,f44])).
% 3.53/0.81  fof(f44,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.53/0.81    inference(cnf_transformation,[],[f2])).
% 3.53/0.81  fof(f2,axiom,(
% 3.53/0.81    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.53/0.81  fof(f388,plain,(
% 3.53/0.81    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))) )),
% 3.53/0.81    inference(superposition,[],[f107,f66])).
% 3.53/0.81  fof(f66,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 3.53/0.81    inference(definition_unfolding,[],[f52,f65])).
% 3.53/0.81  fof(f65,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.53/0.81    inference(definition_unfolding,[],[f47,f64])).
% 3.53/0.81  fof(f64,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.53/0.81    inference(definition_unfolding,[],[f48,f57])).
% 3.53/0.81  fof(f57,plain,(
% 3.53/0.81    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.53/0.81    inference(cnf_transformation,[],[f21])).
% 3.53/0.81  fof(f21,axiom,(
% 3.53/0.81    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.53/0.81  fof(f48,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.53/0.81    inference(cnf_transformation,[],[f20])).
% 3.53/0.81  fof(f20,axiom,(
% 3.53/0.81    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.53/0.81  fof(f47,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.53/0.81    inference(cnf_transformation,[],[f22])).
% 3.53/0.81  fof(f22,axiom,(
% 3.53/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.53/0.81  fof(f52,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.53/0.81    inference(cnf_transformation,[],[f3])).
% 3.53/0.81  fof(f3,axiom,(
% 3.53/0.81    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 3.53/0.81  fof(f107,plain,(
% 3.53/0.81    ( ! [X6,X5] : (r1_tarski(X5,k3_tarski(k2_enumset1(X5,X5,X5,X6)))) )),
% 3.53/0.81    inference(trivial_inequality_removal,[],[f105])).
% 3.53/0.81  fof(f105,plain,(
% 3.53/0.81    ( ! [X6,X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X5,k3_tarski(k2_enumset1(X5,X5,X5,X6)))) )),
% 3.53/0.81    inference(superposition,[],[f55,f71])).
% 3.53/0.81  fof(f71,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.53/0.81    inference(definition_unfolding,[],[f43,f65])).
% 3.53/0.81  fof(f43,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.53/0.81    inference(cnf_transformation,[],[f16])).
% 3.53/0.81  fof(f16,axiom,(
% 3.53/0.81    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.53/0.81  fof(f55,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 3.53/0.81    inference(cnf_transformation,[],[f38])).
% 3.53/0.81  fof(f38,plain,(
% 3.53/0.81    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.53/0.81    inference(nnf_transformation,[],[f6])).
% 3.53/0.81  fof(f6,axiom,(
% 3.53/0.81    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.53/0.81  fof(f7038,plain,(
% 3.53/0.81    ~r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) | spl2_8),
% 3.53/0.81    inference(resolution,[],[f2443,f54])).
% 3.53/0.81  fof(f54,plain,(
% 3.53/0.81    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.53/0.81    inference(cnf_transformation,[],[f30])).
% 3.53/0.81  fof(f30,plain,(
% 3.53/0.81    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.53/0.81    inference(ennf_transformation,[],[f23])).
% 3.53/0.81  fof(f23,axiom,(
% 3.53/0.81    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 3.53/0.81  fof(f2443,plain,(
% 3.53/0.81    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_8),
% 3.53/0.81    inference(avatar_component_clause,[],[f2441])).
% 3.53/0.81  fof(f3711,plain,(
% 3.53/0.81    spl2_11),
% 3.53/0.81    inference(avatar_contradiction_clause,[],[f3702])).
% 3.53/0.81  fof(f3702,plain,(
% 3.53/0.81    $false | spl2_11),
% 3.53/0.81    inference(resolution,[],[f3694,f388])).
% 3.53/0.81  fof(f3694,plain,(
% 3.53/0.81    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | spl2_11),
% 3.53/0.81    inference(resolution,[],[f3480,f54])).
% 3.53/0.81  fof(f3480,plain,(
% 3.53/0.81    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_11),
% 3.53/0.81    inference(avatar_component_clause,[],[f3478])).
% 3.53/0.81  fof(f3478,plain,(
% 3.53/0.81    spl2_11 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.53/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 3.53/0.81  fof(f3485,plain,(
% 3.53/0.81    ~spl2_11 | ~spl2_12),
% 3.53/0.81    inference(avatar_split_clause,[],[f3461,f3482,f3478])).
% 3.53/0.81  fof(f3461,plain,(
% 3.53/0.81    ~r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.53/0.81    inference(resolution,[],[f3256,f63])).
% 3.53/0.81  fof(f63,plain,(
% 3.53/0.81    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.53/0.81    inference(cnf_transformation,[],[f35])).
% 3.53/0.81  fof(f35,plain,(
% 3.53/0.81    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.53/0.81    inference(flattening,[],[f34])).
% 3.53/0.81  fof(f34,plain,(
% 3.53/0.81    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.53/0.81    inference(ennf_transformation,[],[f9])).
% 3.53/0.81  fof(f9,axiom,(
% 3.53/0.81    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 3.53/0.81  fof(f3256,plain,(
% 3.53/0.81    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.53/0.81    inference(backward_demodulation,[],[f68,f3239])).
% 3.53/0.81  fof(f3239,plain,(
% 3.53/0.81    ( ! [X2,X3] : (k3_tarski(k2_enumset1(X2,X2,X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 3.53/0.81    inference(forward_demodulation,[],[f293,f225])).
% 3.53/0.81  fof(f225,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 3.53/0.81    inference(superposition,[],[f67,f72])).
% 3.53/0.81  fof(f72,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.53/0.81    inference(definition_unfolding,[],[f45,f50,f50])).
% 3.53/0.81  fof(f50,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.53/0.81    inference(cnf_transformation,[],[f17])).
% 3.53/0.81  fof(f17,axiom,(
% 3.53/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.53/0.81  fof(f45,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.53/0.81    inference(cnf_transformation,[],[f1])).
% 3.53/0.81  fof(f1,axiom,(
% 3.53/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.53/0.81  fof(f67,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.53/0.81    inference(definition_unfolding,[],[f49,f50])).
% 3.53/0.81  fof(f49,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.53/0.81    inference(cnf_transformation,[],[f7])).
% 3.53/0.81  fof(f7,axiom,(
% 3.53/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.53/0.81  fof(f293,plain,(
% 3.53/0.81    ( ! [X2,X3] : (k3_tarski(k2_enumset1(X2,X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) )),
% 3.53/0.81    inference(superposition,[],[f74,f58])).
% 3.53/0.81  fof(f58,plain,(
% 3.53/0.81    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.53/0.81    inference(cnf_transformation,[],[f18])).
% 3.53/0.81  fof(f18,axiom,(
% 3.53/0.81    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.53/0.81  fof(f74,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.53/0.81    inference(definition_unfolding,[],[f51,f65,f50])).
% 3.53/0.81  fof(f51,plain,(
% 3.53/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.53/0.81    inference(cnf_transformation,[],[f19])).
% 3.53/0.81  fof(f19,axiom,(
% 3.53/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 3.53/0.81  fof(f68,plain,(
% 3.53/0.81    ~r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.53/0.81    inference(definition_unfolding,[],[f39,f65])).
% 3.53/0.81  fof(f39,plain,(
% 3.53/0.81    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.53/0.81    inference(cnf_transformation,[],[f37])).
% 3.53/0.81  fof(f37,plain,(
% 3.53/0.81    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.53/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f36])).
% 3.53/0.81  fof(f36,plain,(
% 3.53/0.81    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.53/0.81    introduced(choice_axiom,[])).
% 3.53/0.81  fof(f28,plain,(
% 3.53/0.81    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 3.53/0.81    inference(ennf_transformation,[],[f25])).
% 3.53/0.81  fof(f25,negated_conjecture,(
% 3.53/0.81    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 3.53/0.81    inference(negated_conjecture,[],[f24])).
% 3.53/0.81  fof(f24,conjecture,(
% 3.53/0.81    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 3.53/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 3.53/0.81  % SZS output end Proof for theBenchmark
% 3.53/0.81  % (3786)------------------------------
% 3.53/0.81  % (3786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.81  % (3786)Termination reason: Refutation
% 3.53/0.81  
% 3.53/0.81  % (3786)Memory used [KB]: 9850
% 3.53/0.81  % (3786)Time elapsed: 0.388 s
% 3.53/0.81  % (3786)------------------------------
% 3.53/0.81  % (3786)------------------------------
% 3.53/0.81  % (3781)Success in time 0.46 s
%------------------------------------------------------------------------------
